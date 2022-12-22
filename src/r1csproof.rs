#![allow(clippy::too_many_arguments)]
use crate::constraints::{VerifierCircuit, VerifierConfig};
use crate::group::{Fq, Fr};
use crate::math::Math;
use crate::parameters::poseidon_params;
use crate::poseidon_transcript::{AppendToPoseidon, PoseidonTranscript};
use crate::sumcheck::SumcheckInstanceProof;
use ark_bls12_377::Bls12_377 as I;
use ark_bw6_761::BW6_761 as P;
use ark_poly::MultilinearExtension;
use ark_poly_commit::multilinear_pc::data_structures::{Commitment, Proof};
use ark_poly_commit::multilinear_pc::MultilinearPC;

use super::commitments::MultiCommitGens;
use super::dense_mlpoly::{DensePolynomial, EqPolynomial, PolyCommitmentGens};
use super::errors::ProofVerifyError;

use super::r1csinstance::R1CSInstance;

use super::scalar::Scalar;
use super::sparse_mlpoly::{SparsePolyEntry, SparsePolynomial};
use super::timer::Timer;
use ark_crypto_primitives::{CircuitSpecificSetupSNARK, SNARK};

use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_serialize::*;
use ark_std::{One, Zero};

use std::time::Instant;

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub struct R1CSProof {
  // The PST commitment to the multilinear extension of the witness.
  comm: Commitment<I>,
  sc_proof_phase1: SumcheckInstanceProof,
  claims_phase2: (Scalar, Scalar, Scalar, Scalar),
  sc_proof_phase2: SumcheckInstanceProof,
  eval_vars_at_ry: Scalar,
  proof_eval_vars_at_ry: Proof<I>,
  rx: Vec<Scalar>,
  ry: Vec<Scalar>,
  // The transcript state after the satisfiability proof was computed.
  pub transcript_sat_state: Scalar,
}
#[derive(Clone)]
pub struct R1CSSumcheckGens {
  gens_1: MultiCommitGens,
  gens_3: MultiCommitGens,
  gens_4: MultiCommitGens,
}

// TODO: fix passing gens_1_ref
impl R1CSSumcheckGens {
  pub fn new(label: &'static [u8], gens_1_ref: &MultiCommitGens) -> Self {
    let gens_1 = gens_1_ref.clone();
    let gens_3 = MultiCommitGens::new(3, label);
    let gens_4 = MultiCommitGens::new(4, label);

    R1CSSumcheckGens {
      gens_1,
      gens_3,
      gens_4,
    }
  }
}

#[derive(Clone)]
pub struct R1CSGens {
  gens_sc: R1CSSumcheckGens,
  gens_pc: PolyCommitmentGens,
}

impl R1CSGens {
  pub fn new(label: &'static [u8], _num_cons: usize, num_vars: usize) -> Self {
    let num_poly_vars = num_vars.log_2();
    let gens_pc = PolyCommitmentGens::new(num_poly_vars, label);
    let gens_sc = R1CSSumcheckGens::new(label, &gens_pc.gens.gens_1);
    R1CSGens { gens_sc, gens_pc }
  }
}

impl R1CSProof {
  fn prove_phase_one(
    num_rounds: usize,
    evals_tau: &mut DensePolynomial,
    evals_Az: &mut DensePolynomial,
    evals_Bz: &mut DensePolynomial,
    evals_Cz: &mut DensePolynomial,
    transcript: &mut PoseidonTranscript,
  ) -> (SumcheckInstanceProof, Vec<Scalar>, Vec<Scalar>) {
    let comb_func =
      |poly_tau_comp: &Scalar,
       poly_A_comp: &Scalar,
       poly_B_comp: &Scalar,
       poly_C_comp: &Scalar|
       -> Scalar { (*poly_tau_comp) * ((*poly_A_comp) * poly_B_comp - poly_C_comp) };

    let (sc_proof_phase_one, r, claims) = SumcheckInstanceProof::prove_cubic_with_additive_term(
      &Scalar::zero(), // claim is zero
      num_rounds,
      evals_tau,
      evals_Az,
      evals_Bz,
      evals_Cz,
      comb_func,
      transcript,
    );

    (sc_proof_phase_one, r, claims)
  }

  fn prove_phase_two(
    num_rounds: usize,
    claim: &Scalar,
    evals_z: &mut DensePolynomial,
    evals_ABC: &mut DensePolynomial,
    transcript: &mut PoseidonTranscript,
  ) -> (SumcheckInstanceProof, Vec<Scalar>, Vec<Scalar>) {
    let comb_func =
      |poly_A_comp: &Scalar, poly_B_comp: &Scalar| -> Scalar { (*poly_A_comp) * poly_B_comp };
    let (sc_proof_phase_two, r, claims) = SumcheckInstanceProof::prove_quad(
      claim, num_rounds, evals_z, evals_ABC, comb_func, transcript,
    );

    (sc_proof_phase_two, r, claims)
  }

  fn protocol_name() -> &'static [u8] {
    b"R1CS proof"
  }

  pub fn prove(
    inst: &R1CSInstance,
    vars: Vec<Scalar>,
    input: &[Scalar],
    gens: &R1CSGens,
    transcript: &mut PoseidonTranscript,
  ) -> (R1CSProof, Vec<Scalar>, Vec<Scalar>) {
    let timer_prove = Timer::new("R1CSProof::prove");
    // we currently require the number of |inputs| + 1 to be at most number of vars
    assert!(input.len() < vars.len());

    // create the multilinear witness polynomial from the satisfying assiment
    let poly_vars = DensePolynomial::new(vars.clone());

    let timer_commit = Timer::new("polycommit");
    // commitment to the satisfying witness polynomial
    let comm = MultilinearPC::<I>::commit(&gens.gens_pc.ck, &poly_vars);
    comm.append_to_poseidon(transcript);
    timer_commit.stop();

    let c = transcript.challenge_scalar();
    transcript.new_from_state(&c);

    transcript.append_scalar_vector(input);

    let timer_sc_proof_phase1 = Timer::new("prove_sc_phase_one");

    // append input to variables to create a single vector z
    let z = {
      let num_inputs = input.len();
      let num_vars = vars.len();
      let mut z = vars;
      z.extend(&vec![Scalar::one()]); // add constant term in z
      z.extend(input);
      z.extend(&vec![Scalar::zero(); num_vars - num_inputs - 1]); // we will pad with zeros
      z
    };

    // derive the verifier's challenge tau
    let (num_rounds_x, num_rounds_y) = (inst.get_num_cons().log_2(), z.len().log_2());
    let tau = transcript.challenge_vector(num_rounds_x);
    // compute the initial evaluation table for R(\tau, x)
    let mut poly_tau = DensePolynomial::new(EqPolynomial::new(tau).evals());
    let (mut poly_Az, mut poly_Bz, mut poly_Cz) =
      inst.multiply_vec(inst.get_num_cons(), z.len(), &z);

    let (sc_proof_phase1, rx, _claims_phase1) = R1CSProof::prove_phase_one(
      num_rounds_x,
      &mut poly_tau,
      &mut poly_Az,
      &mut poly_Bz,
      &mut poly_Cz,
      transcript,
    );
    assert_eq!(poly_tau.len(), 1);
    assert_eq!(poly_Az.len(), 1);
    assert_eq!(poly_Bz.len(), 1);
    assert_eq!(poly_Cz.len(), 1);
    timer_sc_proof_phase1.stop();

    let (tau_claim, Az_claim, Bz_claim, Cz_claim) =
      (&poly_tau[0], &poly_Az[0], &poly_Bz[0], &poly_Cz[0]);
    let prod_Az_Bz_claims = (*Az_claim) * Bz_claim;

    // prove the final step of sum-check #1
    let taus_bound_rx = tau_claim;
    let _claim_post_phase1 = ((*Az_claim) * Bz_claim - Cz_claim) * taus_bound_rx;

    let timer_sc_proof_phase2 = Timer::new("prove_sc_phase_two");
    // combine the three claims into a single claim
    let r_A = transcript.challenge_scalar();
    let r_B = transcript.challenge_scalar();
    let r_C = transcript.challenge_scalar();
    let claim_phase2 = r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim;

    let evals_ABC = {
      // compute the initial evaluation table for R(\tau, x)
      let evals_rx = EqPolynomial::new(rx.clone()).evals();
      let (evals_A, evals_B, evals_C) =
        inst.compute_eval_table_sparse(inst.get_num_cons(), z.len(), &evals_rx);

      assert_eq!(evals_A.len(), evals_B.len());
      assert_eq!(evals_A.len(), evals_C.len());
      (0..evals_A.len())
        .map(|i| r_A * evals_A[i] + r_B * evals_B[i] + r_C * evals_C[i])
        .collect::<Vec<Scalar>>()
    };

    // another instance of the sum-check protocol
    let (sc_proof_phase2, ry, _claims_phase2) = R1CSProof::prove_phase_two(
      num_rounds_y,
      &claim_phase2,
      &mut DensePolynomial::new(z),
      &mut DensePolynomial::new(evals_ABC),
      transcript,
    );
    timer_sc_proof_phase2.stop();

    // TODO: modify the polynomial evaluation in Spartan to be consistent
    // with the evaluation in ark-poly-commit so that reversing is not needed
    // anymore
    let timmer_opening = Timer::new("polyopening");
    let mut dummy = ry[1..].to_vec().clone();
    dummy.reverse();
    let proof_eval_vars_at_ry = MultilinearPC::<I>::open(&gens.gens_pc.ck, &poly_vars, &dummy);
    println!(
      "proof size (no of quotients): {:?}",
      proof_eval_vars_at_ry.proofs.len()
    );
    timmer_opening.stop();

    let timer_polyeval = Timer::new("polyeval");
    let eval_vars_at_ry = poly_vars.evaluate(&ry[1..]);
    timer_polyeval.stop();

    timer_prove.stop();

    let c = transcript.challenge_scalar();

    (
      R1CSProof {
        comm,
        sc_proof_phase1,
        claims_phase2: (*Az_claim, *Bz_claim, *Cz_claim, prod_Az_Bz_claims),
        sc_proof_phase2,
        eval_vars_at_ry,
        proof_eval_vars_at_ry,
        rx: rx.clone(),
        ry: ry.clone(),
        transcript_sat_state: c,
      },
      rx,
      ry,
    )
  }

  pub fn verify_groth16(
    &self,
    num_vars: usize,
    num_cons: usize,
    input: &[Scalar],
    evals: &(Scalar, Scalar, Scalar),
    transcript: &mut PoseidonTranscript,
    gens: &R1CSGens,
  ) -> Result<(u128, u128, u128), ProofVerifyError> {
    self.comm.append_to_poseidon(transcript);

    let c = transcript.challenge_scalar();

    let mut input_as_sparse_poly_entries = vec![SparsePolyEntry::new(0, Scalar::one())];
    //remaining inputs
    input_as_sparse_poly_entries.extend(
      (0..input.len())
        .map(|i| SparsePolyEntry::new(i + 1, input[i]))
        .collect::<Vec<SparsePolyEntry>>(),
    );

    let n = num_vars;
    let input_as_sparse_poly =
      SparsePolynomial::new(n.log_2() as usize, input_as_sparse_poly_entries);

    let config = VerifierConfig {
      num_vars,
      num_cons,
      input: input.to_vec(),
      evals: *evals,
      params: poseidon_params(),
      prev_challenge: c,
      claims_phase2: self.claims_phase2,
      polys_sc1: self.sc_proof_phase1.polys.clone(),
      polys_sc2: self.sc_proof_phase2.polys.clone(),
      eval_vars_at_ry: self.eval_vars_at_ry,
      input_as_sparse_poly,
      // rx: self.rx.clone(),
      ry: self.ry.clone(),
      transcript_sat_state: self.transcript_sat_state,
    };

    let mut rng = ark_std::test_rng();

    let prove_inner = Timer::new("proveinnercircuit");
    let start = Instant::now();
    let circuit = VerifierCircuit::new(&config, &mut rng).unwrap();
    let dp1 = start.elapsed().as_millis();
    prove_inner.stop();

    let start = Instant::now();
    let (pk, vk) = Groth16::<P>::setup(circuit.clone(), &mut rng).unwrap();
    let ds = start.elapsed().as_millis();

    let prove_outer = Timer::new("proveoutercircuit");
    let start = Instant::now();
    let proof = Groth16::<P>::prove(&pk, circuit, &mut rng).unwrap();
    let dp2 = start.elapsed().as_millis();
    prove_outer.stop();

    let start = Instant::now();
    let is_verified = Groth16::<P>::verify(&vk, &[], &proof).unwrap();
    assert!(is_verified);

    let timer_verification = Timer::new("commitverification");
    let mut dummy = self.ry[1..].to_vec();
    // TODO: ensure ark-poly-commit and Spartan produce consistent results
    // when evaluating a polynomial at a given point so this reverse is not
    // needed.
    dummy.reverse();

    // Verifies the proof of opening against the result of evaluating the
    // witness polynomial at point ry.
    let res = MultilinearPC::<I>::check(
      &gens.gens_pc.vk,
      &self.comm,
      &dummy,
      self.eval_vars_at_ry,
      &self.proof_eval_vars_at_ry,
    );

    timer_verification.stop();
    assert!(res == true);
    let dv = start.elapsed().as_millis();

    Ok((ds, dp1 + dp2, dv))
  }

  // Helper function to find the number of constraint in the circuit which
  // requires executing it.
  pub fn circuit_size(
    &self,
    num_vars: usize,
    num_cons: usize,
    input: &[Scalar],
    evals: &(Scalar, Scalar, Scalar),
    transcript: &mut PoseidonTranscript,
    gens: &R1CSGens,
  ) -> Result<usize, ProofVerifyError> {
    self.comm.append_to_poseidon(transcript);

    let c = transcript.challenge_scalar();

    let mut input_as_sparse_poly_entries = vec![SparsePolyEntry::new(0, Scalar::one())];
    //remaining inputs
    input_as_sparse_poly_entries.extend(
      (0..input.len())
        .map(|i| SparsePolyEntry::new(i + 1, input[i]))
        .collect::<Vec<SparsePolyEntry>>(),
    );

    let n = num_vars;
    let input_as_sparse_poly =
      SparsePolynomial::new(n.log_2() as usize, input_as_sparse_poly_entries);

    let config = VerifierConfig {
      num_vars,
      num_cons,
      input: input.to_vec(),
      evals: *evals,
      params: poseidon_params(),
      prev_challenge: c,
      claims_phase2: self.claims_phase2,
      polys_sc1: self.sc_proof_phase1.polys.clone(),
      polys_sc2: self.sc_proof_phase2.polys.clone(),
      eval_vars_at_ry: self.eval_vars_at_ry,
      input_as_sparse_poly,
      // rx: self.rx.clone(),
      ry: self.ry.clone(),
      transcript_sat_state: self.transcript_sat_state,
    };

    let mut rng = ark_std::test_rng();
    let circuit = VerifierCircuit::new(&config, &mut rng).unwrap();

    let nc_inner = verify_constraints_inner(circuit.clone(), &num_cons);

    let nc_outer = verify_constraints_outer(circuit, &num_cons);
    Ok(nc_inner + nc_outer)
  }
}

fn verify_constraints_outer(circuit: VerifierCircuit, _num_cons: &usize) -> usize {
  let cs = ConstraintSystem::<Fq>::new_ref();
  circuit.generate_constraints(cs.clone()).unwrap();
  assert!(cs.is_satisfied().unwrap());
  cs.num_constraints()
}

fn verify_constraints_inner(circuit: VerifierCircuit, _num_cons: &usize) -> usize {
  let cs = ConstraintSystem::<Fr>::new_ref();
  circuit
    .inner_circuit
    .generate_constraints(cs.clone())
    .unwrap();
  assert!(cs.is_satisfied().unwrap());
  cs.num_constraints()
}

#[cfg(test)]
mod tests {
  use crate::parameters::poseidon_params;

  use super::*;

  use ark_std::UniformRand;

  fn produce_tiny_r1cs() -> (R1CSInstance, Vec<Scalar>, Vec<Scalar>) {
    // three constraints over five variables Z1, Z2, Z3, Z4, and Z5
    // rounded to the nearest power of two
    let num_cons = 128;
    let num_vars = 256;
    let num_inputs = 2;

    // encode the above constraints into three matrices
    let mut A: Vec<(usize, usize, Scalar)> = Vec::new();
    let mut B: Vec<(usize, usize, Scalar)> = Vec::new();
    let mut C: Vec<(usize, usize, Scalar)> = Vec::new();

    let one = Scalar::one();
    // constraint 0 entries
    // (Z1 + Z2) * I0 - Z3 = 0;
    A.push((0, 0, one));
    A.push((0, 1, one));
    B.push((0, num_vars + 1, one));
    C.push((0, 2, one));

    // constraint 1 entries
    // (Z1 + I1) * (Z3) - Z4 = 0
    A.push((1, 0, one));
    A.push((1, num_vars + 2, one));
    B.push((1, 2, one));
    C.push((1, 3, one));
    // constraint 3 entries
    // Z5 * 1 - 0 = 0
    A.push((2, 4, one));
    B.push((2, num_vars, one));

    let inst = R1CSInstance::new(num_cons, num_vars, num_inputs, &A, &B, &C);

    // compute a satisfying assignment
    let mut rng = ark_std::rand::thread_rng();
    let i0 = Scalar::rand(&mut rng);
    let i1 = Scalar::rand(&mut rng);
    let z1 = Scalar::rand(&mut rng);
    let z2 = Scalar::rand(&mut rng);
    let z3 = (z1 + z2) * i0; // constraint 1: (Z1 + Z2) * I0 - Z3 = 0;
    let z4 = (z1 + i1) * z3; // constraint 2: (Z1 + I1) * (Z3) - Z4 = 0
    let z5 = Scalar::zero(); //constraint 3

    let mut vars = vec![Scalar::zero(); num_vars];
    vars[0] = z1;
    vars[1] = z2;
    vars[2] = z3;
    vars[3] = z4;
    vars[4] = z5;

    let mut input = vec![Scalar::zero(); num_inputs];
    input[0] = i0;
    input[1] = i1;

    (inst, vars, input)
  }

  #[test]
  fn test_tiny_r1cs() {
    let (inst, vars, input) = tests::produce_tiny_r1cs();
    let is_sat = inst.is_sat(&vars, &input);
    assert!(is_sat);
  }

  #[test]
  fn test_synthetic_r1cs() {
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(1024, 1024, 10);
    let is_sat = inst.is_sat(&vars, &input);
    assert!(is_sat);
  }

  #[test]
  pub fn check_r1cs_proof() {
    let num_vars = 1024;
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    let gens = R1CSGens::new(b"test-m", num_cons, num_vars);

    let params = poseidon_params();
    // let mut random_tape = RandomTape::new(b"proof");

    let mut prover_transcript = PoseidonTranscript::new(&params);
    let (proof, rx, ry) = R1CSProof::prove(&inst, vars, &input, &gens, &mut prover_transcript);

    let inst_evals = inst.evaluate(&rx, &ry);

    let mut verifier_transcript = PoseidonTranscript::new(&params);

    // if you want to check the test fails
    // input[0] = Scalar::zero();

    assert!(proof
      .verify_groth16(
        inst.get_num_vars(),
        inst.get_num_cons(),
        &input,
        &inst_evals,
        &mut verifier_transcript,
        &gens,
      )
      .is_ok());
  }
}
