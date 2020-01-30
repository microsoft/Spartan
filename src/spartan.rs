use super::dense_mlpoly::{EqPolynomial, PolyCommitmentBlinds, PolyCommitmentGens};
use super::errors::ProofVerifyError;
use super::r1csinstance::{
  R1CSCommitment, R1CSCommitmentGens, R1CSDecommitment, R1CSEvalProof, R1CSInstance,
  R1CSInstanceEvals,
};
use super::r1csproof::R1CSProof;
use super::scalar::Scalar;
use super::transcript::{AppendToTranscript, ProofTranscript};
use merlin::Transcript;
use serde::{Deserialize, Serialize};
use std::time::Instant;

#[cfg(test)]
use super::dense_mlpoly::DensePolynomial;
#[cfg(test)]
use super::math::Math;

pub struct SpartanGens {
  gens_z: PolyCommitmentGens,
  gens_r1cs: R1CSCommitmentGens,
}

impl SpartanGens {
  pub fn new(gens_z: PolyCommitmentGens, gens_r1cs: R1CSCommitmentGens) -> SpartanGens {
    SpartanGens { gens_z, gens_r1cs }
  }
}

pub struct SpartanBlinds {
  blinds_z: PolyCommitmentBlinds,
  blind_zr: Scalar,
}

impl SpartanBlinds {
  pub fn new(blinds_z: PolyCommitmentBlinds, blind_zr: Scalar) -> SpartanBlinds {
    SpartanBlinds { blinds_z, blind_zr }
  }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct SpartanProof {
  r1cs_sat_proof: R1CSProof,
  inst_evals: R1CSInstanceEvals,
  r1cs_eval_proof: R1CSEvalProof,
}

#[allow(dead_code)]
impl SpartanProof {
  fn protocol_name() -> &'static [u8] {
    b"Spartan proof"
  }

  /// A public computation to create a commitment to an R1CS instance
  pub fn encode(
    inst: &R1CSInstance,
    gens: &R1CSCommitmentGens,
  ) -> (R1CSCommitment, R1CSDecommitment) {
    inst.commit(gens)
  }

  /// A method to produce a proof of the satisfiability of an R1CS instance
  pub fn prove(
    inst: &R1CSInstance,
    decomm: &R1CSDecommitment,
    vars: Vec<Scalar>,
    input: &Vec<Scalar>,
    blinds: &SpartanBlinds,
    gens: &SpartanGens,
    transcript: &mut Transcript,
  ) -> SpartanProof {
    transcript.append_protocol_name(SpartanProof::protocol_name());
    let (r1cs_sat_proof, rx, ry) = R1CSProof::prove(
      inst,
      vars,
      input,
      &blinds.blinds_z,
      &gens.gens_z,
      &blinds.blind_zr,
      transcript,
    );

    // We send evaluations of A, B, C at r = (rx, ry) as claims
    // to enable the verifier complete the first sum-check
    let start = Instant::now();
    let eval_table_rx = EqPolynomial::new(rx.clone()).evals();
    let eval_table_ry = EqPolynomial::new(ry.clone()).evals();
    let inst_evals = inst.evaluate_with_tables(&eval_table_rx, &eval_table_ry);
    let duration = start.elapsed();
    println!(
      "Evaluating with tables the three polynomials took {:?}",
      duration
    );
    // append the claim of evaluation
    inst_evals.append_to_transcript(b"r1cs_inst_evals", transcript);

    let r1cs_eval_proof =
      R1CSEvalProof::prove(decomm, &rx, &ry, &inst_evals, &gens.gens_r1cs, transcript);

    let r1cs_sat_proof_encoded: Vec<u8> = bincode::serialize(&r1cs_sat_proof).unwrap();
    println!(
      "Length of r1cs_sat_proof_encoded is: {:?}",
      r1cs_sat_proof_encoded.len()
    );

    let r1cs_eval_proof_encoded: Vec<u8> = bincode::serialize(&r1cs_eval_proof).unwrap();
    println!(
      "Length of r1cs_eval_proof_encoded is: {:?}",
      r1cs_eval_proof_encoded.len()
    );

    SpartanProof {
      r1cs_sat_proof,
      inst_evals,
      r1cs_eval_proof,
    }
  }

  /// A method to verify the proof of the satisfiability of an R1CS instance
  pub fn verify(
    &self,
    comm: &R1CSCommitment,
    input: &Vec<Scalar>,
    transcript: &mut Transcript,
    gens: &SpartanGens,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(SpartanProof::protocol_name());

    let start = Instant::now();
    assert_eq!(input.len(), comm.get_num_inputs());
    let (rx, ry) = self
      .r1cs_sat_proof
      .verify(
        comm.get_num_vars(),
        comm.get_num_cons(),
        input,
        &self.inst_evals,
        transcript,
        &gens.gens_z,
      )
      .unwrap();
    let duration = start.elapsed();
    println!("R1CS_sat_proof: Verifier took {:?}", duration);

    let start = Instant::now();
    self
      .inst_evals
      .append_to_transcript(b"r1cs_inst_evals", transcript);
    assert!(self
      .r1cs_eval_proof
      .verify(
        comm,
        &rx,
        &ry,
        &self.inst_evals,
        &gens.gens_r1cs,
        transcript
      )
      .is_ok());
    let duration = start.elapsed();
    println!("R1CS_eval_proof: Verifier took {:?}", duration);
    Ok(())
  }
}

mod tests {
  #[cfg(test)]
  use super::*;
  #[cfg(test)]
  use rand::rngs::OsRng;

  #[allow(dead_code)]
  #[test]
  pub fn check_spartan_proof() {
    let num_vars = 256;
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();
    let m = n.square_root();
    assert_eq!(n, m * m);

    let poly_vars = DensePolynomial::new(vars.clone());
    let r1cs_size = inst.size();

    let gens_z = PolyCommitmentGens::new(poly_vars.get_num_vars(), b"gens_z");
    let gens_r1cs = R1CSCommitmentGens::new(&r1cs_size, b"gens_r1cs");

    // create a commitment to R1CSInstance
    let mut csprng: OsRng = OsRng;
    let (comm, decomm) = SpartanProof::encode(&inst, &gens_r1cs);

    // produce a proof of satisfiability
    let blinds_z = PolyCommitmentBlinds::new(poly_vars.get_num_vars(), &mut csprng);
    let gens = SpartanGens { gens_z, gens_r1cs };
    let blinds = SpartanBlinds {
      blinds_z,
      blind_zr: Scalar::one(),
    };

    let mut prover_transcript = Transcript::new(b"example");
    let proof = SpartanProof::prove(
      &inst,
      &decomm,
      vars,
      &input,
      &blinds,
      &gens,
      &mut prover_transcript,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&comm, &input, &mut verifier_transcript, &gens)
      .is_ok());
  }
}
