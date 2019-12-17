use super::dense_mlpoly::{
  DensePolynomial, EqPolynomial, PolyCommitment, PolyCommitmentBlinds, PolyCommitmentGens,
  PolyEvalProof,
};
use super::errors::ProofVerifyError;
use super::math::Math;
use super::r1csinstance::{R1CSInstance, R1CSInstanceEvals};
use super::scalar::Scalar;
use super::sparse_mlpoly::{
  SparseMatEntry, SparseMatPolynomial, SparsePolyEntry, SparsePolynomial,
};
use super::sumcheck::SumcheckInstanceProof;
use super::transcript::{AppendToTranscript, ProofTranscript};
use super::unipoly::{CubicPoly, QuadPoly, SumcheckProofPolyABI};
use curve25519_dalek::ristretto::CompressedRistretto;
use merlin::Transcript;
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use std::time::Instant;

#[cfg(test)]
use super::scalar::ScalarFromPrimitives;

#[derive(Serialize, Deserialize, Debug)]
pub struct R1CSProof {
  comm_vars: PolyCommitment,
  sc_proof_phase1: SumcheckInstanceProof<CubicPoly>,
  claims_phase2: (Scalar, Scalar, Scalar),
  sc_proof_phase2: SumcheckInstanceProof<QuadPoly>,
  eval_vars_at_ry: Scalar,
  comm_vars_at_ry: CompressedRistretto,
  proof_eval_vars_at_ry: PolyEvalProof,
}

#[allow(dead_code)]
impl R1CSProof {
  fn prove_phase_one(
    num_rounds: usize,
    evals_tau: &mut DensePolynomial,
    evals_Az: &mut DensePolynomial,
    evals_Bz: &mut DensePolynomial,
    evals_Cz: &mut DensePolynomial,
    transcript: &mut Transcript,
  ) -> (SumcheckInstanceProof<CubicPoly>, Vec<Scalar>) {
    // in the first set of rounds, we bound x variables to random values
    let mut e = Scalar::zero();
    let mut r: Vec<Scalar> = Vec::new();
    let mut cubic_polys: Vec<CubicPoly> = Vec::new();
    for _j in 0..num_rounds {
      let mut eval_point_0 = Scalar::zero();
      let mut eval_point_2 = Scalar::zero();
      let mut eval_point_3 = Scalar::zero();
      let len = evals_tau.len() / 2;
      for i in 0..len {
        // eval 0: bound_func is A(low)
        eval_point_0 = &eval_point_0 + &evals_tau[i] * (&evals_Az[i] * &evals_Bz[i] - &evals_Cz[i]);

        // eval 2: bound_func is -A(low) + 2*A(high)
        let tau_bound_point = &evals_tau[len + i] + &evals_tau[len + i] - &evals_tau[i];
        let Az_bound_point = &evals_Az[len + i] + &evals_Az[len + i] - &evals_Az[i];
        let Bz_bound_point = &evals_Bz[len + i] + &evals_Bz[len + i] - &evals_Bz[i];
        let Cz_bound_point = &evals_Cz[len + i] + &evals_Cz[len + i] - &evals_Cz[i];
        eval_point_2 =
          &eval_point_2 + tau_bound_point * (Az_bound_point * Bz_bound_point - Cz_bound_point);

        // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
        let tau_bound_point = &tau_bound_point + &evals_tau[len + i] - &evals_tau[i];
        let Az_bound_point = &Az_bound_point + &evals_Az[len + i] - &evals_Az[i];
        let Bz_bound_point = &Bz_bound_point + &evals_Bz[len + i] - &evals_Bz[i];
        let Cz_bound_point = &Cz_bound_point + &evals_Cz[len + i] - &evals_Cz[i];
        eval_point_3 =
          &eval_point_3 + tau_bound_point * (Az_bound_point * Bz_bound_point - Cz_bound_point);
      }

      let poly = CubicPoly::new(eval_point_0, e - eval_point_0, eval_point_2, eval_point_3);

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");
      r.push(r_j);
      // bound all tables to the verifier's challenege
      evals_tau.bound_poly_var_top(&r_j);
      evals_Az.bound_poly_var_top(&r_j);
      evals_Bz.bound_poly_var_top(&r_j);
      evals_Cz.bound_poly_var_top(&r_j);
      e = poly.evaluate(&r_j);
      cubic_polys.push(poly);
    }

    (SumcheckInstanceProof::new(cubic_polys), r)
  }

  fn prove_phase_two(
    num_rounds: usize,
    claim: &Scalar,
    evals_z: &mut DensePolynomial,
    evals_ABC: &mut DensePolynomial,
    transcript: &mut Transcript,
  ) -> (SumcheckInstanceProof<QuadPoly>, Vec<Scalar>) {
    let comb_func =
      |poly_A_comp: &Scalar, poly_B_comp: &Scalar| -> Scalar { poly_A_comp * poly_B_comp };
    let (sc_proof_phase_two, r, _claims) = SumcheckInstanceProof::<QuadPoly>::prove(
      claim, num_rounds, evals_z, evals_ABC, comb_func, transcript,
    );

    (sc_proof_phase_two, r)
  }

  fn protocol_name() -> &'static [u8] {
    b"R1CS proof"
  }
  pub fn prove(
    inst: &R1CSInstance,
    vars: Vec<Scalar>,
    input: &Vec<Scalar>,
    blinds: &PolyCommitmentBlinds,
    gens: &PolyCommitmentGens,
    blind_eval: &Scalar,
    transcript: &mut Transcript,
  ) -> (R1CSProof, Vec<Scalar>, Vec<Scalar>) {
    transcript.append_protocol_name(R1CSProof::protocol_name());
    // verify if the number of variables is a perfect square. TODO: remove this restriction
    let num_vars = vars.len();
    assert_eq!(num_vars, num_vars.square_root() * num_vars.square_root());
    assert_eq!(num_vars.log2() % 2, 0);

    // we require the number of inputs to be at most number of vars
    let num_inputs = input.len();
    assert!(num_inputs <= num_vars);

    let start = Instant::now();
    // append input to variables to create a single vector z
    let mut z = vars.clone();
    z.extend(input);
    z.extend(&vec![Scalar::zero(); num_vars - num_inputs]); // we will add zeros to the end

    println!("Number of variables to commit is {}", vars.len());
    // create a multilinear polynomial using the supplied assignment for variables
    let poly_vars = DensePolynomial::new(vars);

    // produce a commitment to the satisfying assignment
    let comm_vars = poly_vars.commit(Some(blinds), gens);

    // add the commitment to the prover's transcript
    comm_vars.append_to_transcript(b"poly_commitment", transcript);
    let duration = start.elapsed();
    println!("Time elapsed to commit to vars is: {:?}", duration);

    let start = Instant::now();
    let num_rounds_x = inst.get_num_cons().log2();
    let num_rounds_y = z.len().log2();

    // derive the verifier's challenge tau
    let tau = transcript.challenge_vector(b"challenge_tau", num_rounds_x);

    // compute the initial evaluation table for R(\tau, x)
    let evals_tau = EqPolynomial::new(tau).evals();

    let num_cols = z.len();
    let (evals_Az, evals_Bz, evals_Cz) = inst.multiply_vec(inst.get_num_cons(), num_cols, &z);

    let (mut poly_tau, mut poly_Az, mut poly_Bz, mut poly_Cz) = (
      DensePolynomial::new(evals_tau),
      DensePolynomial::new(evals_Az),
      DensePolynomial::new(evals_Bz),
      DensePolynomial::new(evals_Cz),
    );
    let (sc_proof_phase1, rx) = R1CSProof::prove_phase_one(
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
    let duration = start.elapsed();
    println!("Time elapsed for first sum-check phase is: {:?}", duration);

    let start = Instant::now();
    let (Az_claim, Bz_claim, Cz_claim) = (&poly_Az[0], &poly_Bz[0], &poly_Cz[0]);
    Az_claim.append_to_transcript(b"Az_claim", transcript);
    Bz_claim.append_to_transcript(b"Bz_claim", transcript);
    Cz_claim.append_to_transcript(b"Cz_claim", transcript);

    let r_A = transcript.challenge_scalar(b"challenege_Az");
    let r_B = transcript.challenge_scalar(b"challenege_Bz");
    let r_C = transcript.challenge_scalar(b"challenege_Cz");
    let e = &r_A * Az_claim + &r_B * Bz_claim + &r_C * Cz_claim;

    let evals_z = z;
    // compute the initial evaluation table for R(\tau, x)
    let evals_rx = EqPolynomial::new(rx.clone()).evals();
    let (evals_A, evals_B, evals_C) =
      inst.compute_eval_table_sparse(inst.get_num_cons(), num_cols, &evals_rx);

    assert_eq!(evals_A.len(), evals_B.len());
    assert_eq!(evals_A.len(), evals_C.len());
    let evals_ABC = (0..evals_A.len())
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| r_A * evals_A[i] + r_B * evals_B[i] + r_C * evals_C[i])
      .collect::<Vec<Scalar>>();

    // another instance of the sum-check protocol
    let (sc_proof_phase2, ry) = R1CSProof::prove_phase_two(
      num_rounds_y,
      &e,
      &mut DensePolynomial::new(evals_z),
      &mut DensePolynomial::new(evals_ABC),
      transcript,
    );

    let duration = start.elapsed();
    println!("Time elapsed for second sum-check phase is: {:?}", duration);

    let start = Instant::now();
    let eval_vars_at_ry = poly_vars.evaluate(&ry[1..].to_vec());
    let (proof_eval_vars_at_ry, comm_vars_at_ry) = PolyEvalProof::prove(
      &poly_vars,
      &comm_vars,
      Some(&blinds),
      &ry[1..].to_vec(),
      &eval_vars_at_ry,
      blind_eval,
      &gens,
      transcript,
    );
    let duration = start.elapsed();
    println!("Time elapsed for poly decommit is: {:?}", duration);

    (
      R1CSProof {
        comm_vars,
        sc_proof_phase1,
        claims_phase2: (*Az_claim, *Bz_claim, *Cz_claim),
        sc_proof_phase2,
        eval_vars_at_ry,
        comm_vars_at_ry,
        proof_eval_vars_at_ry,
      },
      rx,
      ry,
    )
  }

  pub fn verify(
    &self,
    num_vars: usize,
    num_cons: usize,
    input: &Vec<Scalar>,
    evals: &R1CSInstanceEvals,
    transcript: &mut Transcript,
    gens: &PolyCommitmentGens,
  ) -> Result<(Vec<Scalar>, Vec<Scalar>), ProofVerifyError> {
    transcript.append_protocol_name(R1CSProof::protocol_name());

    let n = num_vars;
    let m = n.square_root();
    assert_eq!(n, m * m);
    // add the commitment to the verifier's transcript
    self
      .comm_vars
      .append_to_transcript(b"poly_commitment", transcript);

    let num_rounds_x = num_cons.log2();
    let num_rounds_y = (2 * num_vars).log2(); // TODO: fix this.

    // derive the verifier's challenge tau
    let tau = transcript.challenge_vector(b"challenge_tau", num_rounds_x);
    // verify the first sum-check instance
    let (claim, rx) = self
      .sc_proof_phase1
      .verify(Scalar::zero(), num_rounds_x, transcript)
      .unwrap();

    // perform the intermediate sum-check test with claimed Az, Bz, and Cz
    let (Az_claim, Bz_claim, Cz_claim) = self.claims_phase2;
    transcript.append_scalar(b"Az_claim", &Az_claim);
    transcript.append_scalar(b"Bz_claim", &Bz_claim);
    transcript.append_scalar(b"Cz_claim", &Cz_claim);
    let taus_bound_r: Scalar = (0..rx.len())
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| &rx[i] * &tau[i] + (&Scalar::one() - &rx[i]) * (&Scalar::one() - &tau[i]))
      .product();
    let e_claim = &taus_bound_r * (&Az_claim * &Bz_claim - &Cz_claim);
    assert_eq!(e_claim, claim);

    // derive three public challenges and then derive a joint claim
    let r_A = transcript.challenge_scalar(b"challenege_Az");
    let r_B = transcript.challenge_scalar(b"challenege_Bz");
    let r_C = transcript.challenge_scalar(b"challenege_Cz");
    let joint_claim = r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim;

    // verify the joint claim with a sum-check protocol
    let (joint_claim_e, ry) = self
      .sc_proof_phase2
      .verify(joint_claim, num_rounds_y, transcript)
      .unwrap();

    // verify Z(ry) proof against the initial commitment. TODO: verify c_eval = C(eval)
    assert!(self
      .proof_eval_vars_at_ry
      .verify(
        gens,
        transcript,
        &ry[1..].to_vec(),
        &self.comm_vars_at_ry,
        &self.comm_vars
      )
      .is_ok());

    let input_as_sparse_poly_entries = (0..input.len())
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| SparsePolyEntry::new(i, input[i]))
      .collect::<Vec<SparsePolyEntry>>();

    let poly_input = SparsePolynomial::new(n.log2(), input_as_sparse_poly_entries);
    let poly_input_eval = poly_input.evaluate(&ry[1..].to_vec());

    let eval_Z_at_ry = (Scalar::one() - ry[0]) * self.eval_vars_at_ry + ry[0] * poly_input_eval;

    let (eval_A_r, eval_B_r, eval_C_r) = evals.get_evaluations();

    // perform the final check in the second sum-check protocol
    let joint_claim_e_expected = r_A * (eval_A_r * eval_Z_at_ry)
      + r_B * (eval_B_r * eval_Z_at_ry)
      + r_C * (eval_C_r * eval_Z_at_ry);
    assert_eq!(joint_claim_e_expected, joint_claim_e);

    Ok((rx, ry))
  }
}

mod tests {
  use super::*;

  #[allow(dead_code)]
  fn produce_tiny_r1cs() -> (R1CSInstance, Vec<Scalar>, Vec<Scalar>) {
    // three constraints over five variables Z1, Z2, Z3, Z4, and Z5
    // rounded to the nearest power of two
    let num_cons = 128;
    let num_vars = 256; // includes a slot for constant term; must be a perfect square, so round up.
    let num_inputs = 2;

    // encode the above constraints into three matrices
    let mut A: Vec<SparseMatEntry> = Vec::new();
    let mut B: Vec<SparseMatEntry> = Vec::new();
    let mut C: Vec<SparseMatEntry> = Vec::new();

    let one = Scalar::one();
    // constraint 0 entries
    // (Z1 + Z2) * I0 - Z3 = 0;
    A.push(SparseMatEntry::new(0, 1, one));
    A.push(SparseMatEntry::new(0, 2, one));
    B.push(SparseMatEntry::new(0, num_vars, one));
    C.push(SparseMatEntry::new(0, 3, one));

    // constraint 1 entries
    // (Z1 + I1) * (Z3) - Z4 = 0
    A.push(SparseMatEntry::new(1, 1, one));
    A.push(SparseMatEntry::new(1, num_vars + 1, one));
    B.push(SparseMatEntry::new(1, 3, one));
    C.push(SparseMatEntry::new(1, 4, one));
    // constraint 3 entries
    // Z5 * 1 - 0 = 0
    A.push(SparseMatEntry::new(2, 5, one));
    B.push(SparseMatEntry::new(2, 0, one));

    let num_vars_x = num_cons.log2();
    let num_vars_y = (2 * num_vars).log2();

    let poly_A = SparseMatPolynomial::new(num_vars_x, num_vars_y, A);
    let poly_B = SparseMatPolynomial::new(num_vars_x, num_vars_y, B);
    let poly_C = SparseMatPolynomial::new(num_vars_x, num_vars_y, C);

    let inst = R1CSInstance::new(num_cons, num_vars, num_inputs, poly_A, poly_B, poly_C);

    // compute a satisfying assignment
    let mut csprng: OsRng = OsRng;
    let i0 = Scalar::random(&mut csprng);
    let i1 = Scalar::random(&mut csprng);
    let z1 = Scalar::random(&mut csprng);
    let z2 = Scalar::random(&mut csprng);
    let z3 = (z1 + z2) * i0; // constraint 1: (Z1 + Z2) * I0 - Z3 = 0;
    let z4 = (z1 + i1) * z3; // constraint 2: (Z1 + I1) * (Z3) - Z4 = 0
    let z5 = Scalar::zero(); //constraint 3

    let mut vars = vec![Scalar::zero(); num_vars];
    vars[0] = Scalar::one(); // constant always set to 1
    vars[1] = z1;
    vars[2] = z2;
    vars[3] = z3;
    vars[4] = z4;
    vars[5] = z5;

    let mut input = vec![Scalar::zero(); num_inputs];
    input[0] = i0;
    input[1] = i1;

    (inst, vars, input)
  }

  #[test]
  fn test_tiny_r1cs() {
    let (inst, vars, input) = tests::produce_tiny_r1cs();
    let is_sat = inst.is_sat(&vars, &input);
    assert_eq!(is_sat, true);
  }

  #[test]
  fn test_synthetic_r1cs() {
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(1024, 1024 - 10, 10);
    let is_sat = inst.is_sat(&vars, &input);
    assert_eq!(is_sat, true);
  }

  #[test]
  fn test_cubic_poly_interpolation() {
    let mut csprng: OsRng = OsRng;

    // generate a random polynomial in point-value form
    let poly = CubicPoly::new(
      Scalar::random(&mut csprng),
      Scalar::random(&mut csprng),
      Scalar::random(&mut csprng),
      Scalar::random(&mut csprng),
    );

    assert_eq!(poly.evaluate(&Scalar::zero()), poly.eval_at_zero());
    assert_eq!(poly.evaluate(&Scalar::one()), poly.eval_at_one());
    assert_eq!(poly.evaluate(&(2 as usize).to_scalar()), poly.eval_at_two());
    assert_eq!(
      poly.evaluate(&(3 as usize).to_scalar()),
      poly.eval_at_three()
    );
  }

  #[test]
  pub fn check_r1cs_proof() {
    let num_vars = 1024;
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();
    let m = n.square_root();
    assert_eq!(n, m * m);

    let poly_vars = DensePolynomial::new(vars.clone());
    let poly_vars_size = poly_vars.size();

    let gens = PolyCommitmentGens::new(&poly_vars_size, b"test-m");
    let mut csprng: OsRng = OsRng;
    let blinds = PolyCommitmentBlinds::new(&poly_vars_size, &mut csprng);

    let mut prover_transcript = Transcript::new(b"example");
    let (proof, rx, ry) = R1CSProof::prove(
      &inst,
      vars,
      &input,
      &blinds,
      &gens,
      &Scalar::one(),
      &mut prover_transcript,
    );

    let eval_table_rx = EqPolynomial::new(rx).evals();
    let eval_table_ry = EqPolynomial::new(ry).evals();
    let inst_evals = inst.evaluate_with_tables(&eval_table_rx, &eval_table_ry);

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(
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
