use super::commitments::{Commitments, MultiCommitGens};
use super::dense_mlpoly::{
  DensePolynomial, EqPolynomial, PolyCommitment, PolyCommitmentBlinds, PolyCommitmentGens,
  PolyEvalProof,
};
use super::errors::ProofVerifyError;
use super::math::Math;
use super::nizk::{EqualityProof, KnowledgeProof, ProductProof};
use super::r1csinstance::{R1CSInstance, R1CSInstanceEvals};
use super::scalar::{Scalar, ScalarBytes, ScalarBytesFromScalar};
use super::sparse_mlpoly::{
  SparseMatEntry, SparseMatPolynomial, SparsePolyEntry, SparsePolynomial,
};
use super::sumcheck::ZKSumcheckInstanceProof;
use super::timer::Timer;
use super::transcript::{AppendToTranscript, ProofTranscript};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use std::iter;

#[derive(Serialize, Deserialize, Debug)]
pub struct R1CSProof {
  comm_vars: PolyCommitment,
  sc_proof_phase1: ZKSumcheckInstanceProof,
  claims_phase2: (
    CompressedRistretto,
    CompressedRistretto,
    CompressedRistretto,
    CompressedRistretto,
  ),
  pok_claims_phase2: (KnowledgeProof, ProductProof),
  proof_eq_sc_phase1: EqualityProof,
  sc_proof_phase2: ZKSumcheckInstanceProof,
  comm_vars_at_ry: CompressedRistretto,
  proof_eval_vars_at_ry: PolyEvalProof,
  proof_eq_sc_phase2: EqualityProof,
}

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

pub struct R1CSSumcheckBlinds {
  blinds_phase_one: (Vec<Scalar>, Vec<Scalar>),
  blinds_phase_two: (Vec<Scalar>, Vec<Scalar>),
}

impl R1CSSumcheckBlinds {
  pub fn new(num_cons: usize, num_vars: usize, csprng: &mut OsRng) -> Self {
    let blinds_phase_one = (
      (0..num_cons.log2())
        .map(|_i| Scalar::random(csprng))
        .collect::<Vec<Scalar>>(),
      (0..num_cons.log2())
        .map(|_i| Scalar::random(csprng))
        .collect::<Vec<Scalar>>(),
    );
    let blinds_phase_two = (
      (0..(2 * num_vars).log2())
        .map(|_i| Scalar::random(csprng))
        .collect::<Vec<Scalar>>(),
      (0..(2 * num_vars).log2())
        .map(|_i| Scalar::random(csprng))
        .collect::<Vec<Scalar>>(),
    );
    R1CSSumcheckBlinds {
      blinds_phase_one,
      blinds_phase_two,
    }
  }
}

pub struct R1CSGens {
  gens_sc: R1CSSumcheckGens,
  gens_pc: PolyCommitmentGens,
}

impl R1CSGens {
  pub fn new(_num_cons: usize, num_vars: usize, label: &'static [u8]) -> Self {
    let num_poly_vars = num_vars.log2();
    let gens_pc = PolyCommitmentGens::new(num_poly_vars, label);
    let gens_sc = R1CSSumcheckGens::new(label, &gens_pc.gens.gens_1);
    R1CSGens { gens_sc, gens_pc }
  }
}

pub struct R1CSBlinds {
  blinds_sc: R1CSSumcheckBlinds,
  blinds_pc: PolyCommitmentBlinds,
}

impl R1CSBlinds {
  pub fn new(num_cons: usize, num_vars: usize) -> Self {
    let mut csprng: OsRng = OsRng;
    let blinds_sc = R1CSSumcheckBlinds::new(num_cons, num_vars, &mut csprng);
    let num_poly_vars = num_vars.log2();
    let blinds_pc = PolyCommitmentBlinds::new(num_poly_vars, &mut csprng);
    R1CSBlinds {
      blinds_sc,
      blinds_pc,
    }
  }
}

#[allow(dead_code)]
impl R1CSProof {
  fn prove_phase_one(
    num_rounds: usize,
    evals_tau: &mut DensePolynomial,
    evals_Az: &mut DensePolynomial,
    evals_Bz: &mut DensePolynomial,
    evals_Cz: &mut DensePolynomial,
    gens: &R1CSSumcheckGens,
    blinds: &(Vec<Scalar>, Vec<Scalar>),
    transcript: &mut Transcript,
  ) -> (ZKSumcheckInstanceProof, Vec<Scalar>, Vec<Scalar>, Scalar) {
    let comb_func = |poly_A_comp: &Scalar,
                     poly_B_comp: &Scalar,
                     poly_C_comp: &Scalar,
                     poly_D_comp: &Scalar|
     -> Scalar { poly_A_comp * (poly_B_comp * poly_C_comp - poly_D_comp) };

    let (sc_proof_phase_one, r, claims, blind_claim_postsc) =
      ZKSumcheckInstanceProof::prove_cubic_with_additive_term(
        &Scalar::zero(), // claim is zero
        &Scalar::zero(), // blind for claim is also zero
        num_rounds,
        evals_tau,
        evals_Az,
        evals_Bz,
        evals_Cz,
        comb_func,
        &gens.gens_1,
        &gens.gens_4,
        blinds,
        transcript,
      );

    (sc_proof_phase_one, r, claims, blind_claim_postsc)
  }

  fn prove_phase_two(
    num_rounds: usize,
    claim: &Scalar,
    blind_claim: &Scalar,
    evals_z: &mut DensePolynomial,
    evals_ABC: &mut DensePolynomial,
    gens: &R1CSSumcheckGens,
    blinds: &(Vec<Scalar>, Vec<Scalar>),
    transcript: &mut Transcript,
  ) -> (ZKSumcheckInstanceProof, Vec<Scalar>, Vec<Scalar>, Scalar) {
    let comb_func =
      |poly_A_comp: &Scalar, poly_B_comp: &Scalar| -> Scalar { poly_A_comp * poly_B_comp };
    let (sc_proof_phase_two, r, claims, blind_claim_postsc) = ZKSumcheckInstanceProof::prove_quad(
      claim,
      blind_claim,
      num_rounds,
      evals_z,
      evals_ABC,
      comb_func,
      &gens.gens_1,
      &gens.gens_3,
      blinds,
      transcript,
    );

    (sc_proof_phase_two, r, claims, blind_claim_postsc)
  }

  fn protocol_name() -> &'static [u8] {
    b"R1CS proof"
  }

  pub fn prove(
    inst: &R1CSInstance,
    vars: Vec<Scalar>,
    input: &Vec<Scalar>,
    blinds: &R1CSBlinds,
    gens: &R1CSGens,
    blind_eval: &Scalar,
    transcript: &mut Transcript,
  ) -> (R1CSProof, Vec<Scalar>, Vec<Scalar>) {
    let mut csprng: OsRng = OsRng;
    let timer_prove = Timer::new("R1CSProof::prove");
    transcript.append_protocol_name(R1CSProof::protocol_name());

    // we currently require the number of inputs to be at most number of vars
    let num_inputs = input.len();
    assert!(num_inputs <= vars.len());

    let timer_commit = Timer::new("polycommit");
    // append input to variables to create a single vector z
    let z = {
      let mut z = vars.clone();
      z.extend(input);
      z.extend(&vec![Scalar::zero(); vars.len() - num_inputs]); // we will pad with zeros
      z
    };

    // create a multilinear polynomial using the supplied assignment for variables
    let poly_vars = DensePolynomial::new(vars);

    // produce a commitment to the satisfying assignment
    let comm_vars = poly_vars.commit(Some(&blinds.blinds_pc), &gens.gens_pc);

    // add the commitment to the prover's transcript
    comm_vars.append_to_transcript(b"poly_commitment", transcript);
    timer_commit.stop();

    let (num_rounds_x, num_rounds_y) = (inst.get_num_cons().log2(), z.len().log2());
    let timer_sc_proof_phase1 = Timer::new("prove_sc_phase_one");

    // derive the verifier's challenge tau
    let tau = transcript.challenge_vector(b"challenge_tau", num_rounds_x);

    // compute the initial evaluation table for R(\tau, x)
    let mut poly_tau = DensePolynomial::new(EqPolynomial::new(tau.clone()).evals());
    let num_cols = z.len();
    let (mut poly_Az, mut poly_Bz, mut poly_Cz) =
      inst.multiply_vec(inst.get_num_cons(), num_cols, &z);

    let (sc_proof_phase1, rx, _claims_phase1, blind_claim_postsc1) = R1CSProof::prove_phase_one(
      num_rounds_x,
      &mut poly_tau,
      &mut poly_Az,
      &mut poly_Bz,
      &mut poly_Cz,
      &gens.gens_sc,
      &blinds.blinds_sc.blinds_phase_one,
      transcript,
    );
    assert_eq!(poly_tau.len(), 1);
    assert_eq!(poly_Az.len(), 1);
    assert_eq!(poly_Bz.len(), 1);
    assert_eq!(poly_Cz.len(), 1);
    timer_sc_proof_phase1.stop();

    let (Az_claim, Bz_claim, Cz_claim) = (&poly_Az[0], &poly_Bz[0], &poly_Cz[0]);
    let (Az_blind, Bz_blind, Cz_blind, prod_Az_Bz_blind) = (
      Scalar::random(&mut csprng),
      Scalar::random(&mut csprng),
      Scalar::random(&mut csprng),
      Scalar::random(&mut csprng),
    );

    let (pok_Cz_claim, comm_Cz_claim) = {
      // randomness for the knowledge proof
      let (Cz_t1, Cz_t2) = (Scalar::random(&mut csprng), Scalar::random(&mut csprng));

      KnowledgeProof::prove(
        &gens.gens_sc.gens_1,
        transcript,
        &Cz_claim,
        &Cz_blind,
        &Cz_t1,
        &Cz_t2,
      )
    };

    let (proof_prod, comm_Az_claim, comm_Bz_claim, comm_prod_Az_Bz_claims) = {
      // randomness for the product proof
      let (b1, b2, b3, b4, b5) = (
        Scalar::random(&mut csprng),
        Scalar::random(&mut csprng),
        Scalar::random(&mut csprng),
        Scalar::random(&mut csprng),
        Scalar::random(&mut csprng),
      );
      let prod = Az_claim * Bz_claim;
      ProductProof::prove(
        &gens.gens_sc.gens_1,
        transcript,
        &Az_claim,
        &Az_blind,
        &Bz_claim,
        &Bz_blind,
        &prod,
        &prod_Az_Bz_blind,
        &b1,
        &b2,
        &b3,
        &b4,
        &b5,
      )
    };

    comm_Az_claim.append_to_transcript(b"comm_Az_claim", transcript);
    comm_Bz_claim.append_to_transcript(b"comm_Bz_claim", transcript);
    comm_Cz_claim.append_to_transcript(b"comm_Cz_claim", transcript);
    comm_prod_Az_Bz_claims.append_to_transcript(b"comm_prod_Az_Bz_claims", transcript);

    // prove the final step of sum-check #1
    let taus_bound_rx: Scalar = (0..rx.len())
      .map(|i| &rx[i] * &tau[i] + (&Scalar::one() - &rx[i]) * (&Scalar::one() - &tau[i]))
      .product();
    let blind_expected_claim_postsc1 = &taus_bound_rx * (&prod_Az_Bz_blind - &Cz_blind);
    let claim_post_phase1 = (Az_claim * Bz_claim - Cz_claim) * &taus_bound_rx;
    let r = Scalar::random(&mut csprng);
    let (proof_eq_sc_phase1, _C1, _C2) = EqualityProof::prove(
      &gens.gens_sc.gens_1,
      transcript,
      &claim_post_phase1,
      &blind_expected_claim_postsc1,
      &claim_post_phase1,
      &blind_claim_postsc1,
      &r,
    );

    let timer_sc_proof_phase2 = Timer::new("prove_sc_phase_two");
    // combine the three claims into a single claim
    let r_A = transcript.challenge_scalar(b"challenege_Az");
    let r_B = transcript.challenge_scalar(b"challenege_Bz");
    let r_C = transcript.challenge_scalar(b"challenege_Cz");
    let claim_phase2 = &r_A * Az_claim + &r_B * Bz_claim + &r_C * Cz_claim;
    let blind_claim_phase2 = &r_A * Az_blind + &r_B * Bz_blind + &r_C * Cz_blind;

    let evals_z = z;
    // compute the initial evaluation table for R(\tau, x)
    let evals_rx = EqPolynomial::new(rx.clone()).evals();
    let (evals_A, evals_B, evals_C) =
      inst.compute_eval_table_sparse(inst.get_num_cons(), num_cols, &evals_rx);

    assert_eq!(evals_A.len(), evals_B.len());
    assert_eq!(evals_A.len(), evals_C.len());
    let evals_ABC = (0..evals_A.len())
      .map(|i| &r_A * &evals_A[i] + &r_B * &evals_B[i] + &r_C * &evals_C[i])
      .collect::<Vec<Scalar>>();

    // another instance of the sum-check protocol
    let (sc_proof_phase2, ry, claims_phase2, blind_claim_postsc2) = R1CSProof::prove_phase_two(
      num_rounds_y,
      &claim_phase2,
      &blind_claim_phase2,
      &mut DensePolynomial::new(evals_z),
      &mut DensePolynomial::new(evals_ABC),
      &gens.gens_sc,
      &blinds.blinds_sc.blinds_phase_two,
      transcript,
    );
    timer_sc_proof_phase2.stop();

    let timer_polyeval = Timer::new("polyeval");
    let eval_vars_at_ry = poly_vars.evaluate(&ry[1..].to_vec());
    let (proof_eval_vars_at_ry, comm_vars_at_ry) = PolyEvalProof::prove(
      &poly_vars,
      Some(&blinds.blinds_pc),
      &ry[1..].to_vec(),
      &eval_vars_at_ry,
      Some(blind_eval),
      &gens.gens_pc,
      transcript,
    );
    timer_polyeval.stop();

    // prove the final step of sum-check #2
    let blind_eval_Z_at_ry = (Scalar::one() - &ry[0]) * blind_eval;
    let blind_expected_claim_postsc2 = &claims_phase2[1] * &blind_eval_Z_at_ry;
    let claim_post_phase2 = &claims_phase2[0] * &claims_phase2[1];
    let r2 = Scalar::random(&mut csprng);
    let (proof_eq_sc_phase2, _C1, _C2) = EqualityProof::prove(
      &gens.gens_pc.gens.gens_1,
      transcript,
      &claim_post_phase2,
      &blind_expected_claim_postsc2,
      &claim_post_phase2,
      &blind_claim_postsc2,
      &r2,
    );

    timer_prove.stop();

    (
      R1CSProof {
        comm_vars,
        sc_proof_phase1,
        claims_phase2: (
          comm_Az_claim,
          comm_Bz_claim,
          comm_Cz_claim,
          comm_prod_Az_Bz_claims,
        ),
        pok_claims_phase2: (pok_Cz_claim, proof_prod),
        proof_eq_sc_phase1,
        sc_proof_phase2,
        comm_vars_at_ry,
        proof_eval_vars_at_ry,
        proof_eq_sc_phase2,
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
    gens: &R1CSGens,
  ) -> Result<(Vec<Scalar>, Vec<Scalar>), ProofVerifyError> {
    transcript.append_protocol_name(R1CSProof::protocol_name());

    let n = num_vars;
    // add the commitment to the verifier's transcript
    self
      .comm_vars
      .append_to_transcript(b"poly_commitment", transcript);

    let (num_rounds_x, num_rounds_y) = (num_cons.log2(), (2 * num_vars).log2());

    // derive the verifier's challenge tau
    let tau = transcript.challenge_vector(b"challenge_tau", num_rounds_x);

    // verify the first sum-check instance
    let claim_phase1 = Scalar::zero()
      .commit(&Scalar::zero(), &gens.gens_sc.gens_1)
      .compress();
    let (comm_claim_post_phase1, rx) = self
      .sc_proof_phase1
      .verify(
        &claim_phase1,
        num_rounds_x,
        3,
        &gens.gens_sc.gens_1,
        &gens.gens_sc.gens_4,
        transcript,
      )
      .unwrap();

    // perform the intermediate sum-check test with claimed Az, Bz, and Cz
    let (comm_Az_claim, comm_Bz_claim, comm_Cz_claim, comm_prod_Az_Bz_claims) = &self.claims_phase2;
    let (pok_Cz_claim, proof_prod) = &self.pok_claims_phase2;

    assert!(pok_Cz_claim
      .verify(&gens.gens_sc.gens_1, transcript, &comm_Cz_claim)
      .is_ok());
    assert!(proof_prod
      .verify(
        &gens.gens_sc.gens_1,
        transcript,
        &comm_Az_claim,
        &comm_Bz_claim,
        &comm_prod_Az_Bz_claims
      )
      .is_ok());

    comm_Az_claim.append_to_transcript(b"comm_Az_claim", transcript);
    comm_Bz_claim.append_to_transcript(b"comm_Bz_claim", transcript);
    comm_Cz_claim.append_to_transcript(b"comm_Cz_claim", transcript);
    comm_prod_Az_Bz_claims.append_to_transcript(b"comm_prod_Az_Bz_claims", transcript);

    let taus_bound_rx: Scalar = (0..rx.len())
      .map(|i| &rx[i] * &tau[i] + (&Scalar::one() - &rx[i]) * (&Scalar::one() - &tau[i]))
      .product();
    let expected_claim_post_phase1 = (Scalar::decompress_scalar(&taus_bound_rx)
      * (comm_prod_Az_Bz_claims.decompress().unwrap() - comm_Cz_claim.decompress().unwrap()))
    .compress();

    // verify proof that expected_claim_post_phase1 == claim_post_phase1
    assert!(self
      .proof_eq_sc_phase1
      .verify(
        &gens.gens_sc.gens_1,
        transcript,
        &expected_claim_post_phase1,
        &comm_claim_post_phase1,
      )
      .is_ok());

    // derive three public challenges and then derive a joint claim
    let r_A = transcript.challenge_scalar(b"challenege_Az");
    let r_B = transcript.challenge_scalar(b"challenege_Bz");
    let r_C = transcript.challenge_scalar(b"challenege_Cz");

    // r_A * comm_Az_claim + r_B * comm_Bz_claim + r_C * comm_Cz_claim;
    let comm_claim_phase2 = RistrettoPoint::vartime_multiscalar_mul(
      iter::once(&r_A)
        .chain(iter::once(&r_B))
        .chain(iter::once(&r_C))
        .map(|s| Scalar::decompress_scalar(&s))
        .collect::<Vec<ScalarBytes>>(),
      iter::once(&comm_Az_claim)
        .chain(iter::once(&comm_Bz_claim))
        .chain(iter::once(&comm_Cz_claim))
        .map(|pt| pt.decompress().unwrap())
        .collect::<Vec<RistrettoPoint>>(),
    )
    .compress();

    // verify the joint claim with a sum-check protocol
    let (comm_claim_post_phase2, ry) = self
      .sc_proof_phase2
      .verify(
        &comm_claim_phase2,
        num_rounds_y,
        2,
        &gens.gens_sc.gens_1,
        &gens.gens_sc.gens_3,
        transcript,
      )
      .unwrap();

    // verify Z(ry) proof against the initial commitment
    assert!(self
      .proof_eval_vars_at_ry
      .verify(
        &gens.gens_pc,
        transcript,
        &ry[1..].to_vec(),
        &self.comm_vars_at_ry,
        &self.comm_vars
      )
      .is_ok());

    let input_as_sparse_poly_entries = (0..input.len())
      .map(|i| SparsePolyEntry::new(i, input[i]))
      .collect::<Vec<SparsePolyEntry>>();
    let poly_input_eval =
      SparsePolynomial::new(n.log2(), input_as_sparse_poly_entries).evaluate(&ry[1..].to_vec());

    // compute commitment to eval_Z_at_ry = (Scalar::one() - ry[0]) * self.eval_vars_at_ry + ry[0] * poly_input_eval
    // TODO: ensure the constant term in z is actually 1.
    let comm_eval_Z_at_ry = RistrettoPoint::vartime_multiscalar_mul(
      iter::once(Scalar::one() - &ry[0])
        .chain(iter::once(ry[0]))
        .map(|s| Scalar::decompress_scalar(&s))
        .collect::<Vec<ScalarBytes>>(),
      iter::once(&self.comm_vars_at_ry.decompress().unwrap()).chain(iter::once(
        &poly_input_eval.commit(&Scalar::zero(), &gens.gens_pc.gens.gens_1),
      )),
    );

    // perform the final check in the second sum-check protocol
    let (eval_A_r, eval_B_r, eval_C_r) = evals.get_evaluations();
    let expected_claim_post_phase2 =
      (Scalar::decompress_scalar(&(&r_A * &eval_A_r + &r_B * &eval_B_r + &r_C * &eval_C_r))
        * comm_eval_Z_at_ry)
        .compress();
    // verify proof that expected_claim_post_phase1 == claim_post_phase1
    assert!(self
      .proof_eq_sc_phase2
      .verify(
        &gens.gens_sc.gens_1,
        transcript,
        &expected_claim_post_phase2,
        &comm_claim_post_phase2,
      )
      .is_ok());

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
  pub fn check_r1cs_proof() {
    let num_vars = 1024;
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();
    let m = n.square_root();
    assert_eq!(n, m * m);

    let gens = R1CSGens::new(num_cons, num_vars, b"test-m");
    let blinds = R1CSBlinds::new(num_cons, num_vars);

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
