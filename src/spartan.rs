use super::dense_mlpoly::EqPolynomial;
use super::errors::ProofVerifyError;
use super::r1csinstance::{
  R1CSCommitment, R1CSCommitmentGens, R1CSDecommitment, R1CSEvalProof, R1CSInstance,
  R1CSInstanceEvals,
};
use super::r1csproof::{R1CSGens, R1CSProof};
use super::scalar::Scalar;
use super::timer::Timer;
use super::transcript::{AppendToTranscript, ProofTranscript};
use merlin::Transcript;
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

pub struct SpartanGens {
  gens_r1cs_sat: R1CSGens,
  gens_r1cs_eval: R1CSCommitmentGens,
}

impl SpartanGens {
  pub fn new(gens_r1cs_sat: R1CSGens, gens_r1cs_eval: R1CSCommitmentGens) -> SpartanGens {
    SpartanGens {
      gens_r1cs_sat,
      gens_r1cs_eval,
    }
  }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct SpartanProof {
  r1cs_sat_proof: R1CSProof,
  inst_evals: R1CSInstanceEvals,
  r1cs_eval_proof: R1CSEvalProof,
}

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
    gens: &SpartanGens,
    transcript: &mut Transcript,
  ) -> SpartanProof {
    // we create a Transcript object seeded with a random Scalar
    // to aid the prover produce its randomness
    let mut random_tape = {
      let mut csprng: OsRng = OsRng;
      let mut tape = Transcript::new(b"SpartanProof");
      tape.append_scalar(b"init_randomness", &Scalar::random(&mut csprng));
      tape
    };

    transcript.append_protocol_name(SpartanProof::protocol_name());
    let (r1cs_sat_proof, rx, ry) = {
      let (proof, rx, ry) = R1CSProof::prove(
        inst,
        vars,
        input,
        &gens.gens_r1cs_sat,
        transcript,
        &mut random_tape,
      );
      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, rx, ry)
    };

    // We send evaluations of A, B, C at r = (rx, ry) as claims
    // to enable the verifier complete the first sum-check
    let timer_eval = Timer::new("eval_sparse_polys");
    let inst_evals = {
      let eval_table_rx = EqPolynomial::new(rx.clone()).evals();
      let eval_table_ry = EqPolynomial::new(ry.clone()).evals();
      inst.evaluate_with_tables(&eval_table_rx, &eval_table_ry)
    };
    inst_evals.append_to_transcript(b"r1cs_inst_evals", transcript);
    timer_eval.stop();

    let r1cs_eval_proof = {
      let proof = R1CSEvalProof::prove(
        decomm,
        &rx,
        &ry,
        &inst_evals,
        &gens.gens_r1cs_eval,
        transcript,
        &mut random_tape,
      );

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
      proof
    };

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

    let timer_sat_proof = Timer::new("verify_sat_proof");
    assert_eq!(input.len(), comm.get_num_inputs());
    let (rx, ry) = self
      .r1cs_sat_proof
      .verify(
        comm.get_num_vars(),
        comm.get_num_cons(),
        input,
        &self.inst_evals,
        transcript,
        &gens.gens_r1cs_sat,
      )
      .unwrap();
    timer_sat_proof.stop();

    let timer_eval_proof = Timer::new("verify_eval_proof");
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
        &gens.gens_r1cs_eval,
        transcript
      )
      .is_ok());
    timer_eval_proof.stop();
    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  pub fn check_spartan_proof() {
    let num_vars = 256;
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    let r1cs_size = inst.size();
    let gens_r1cs_eval = R1CSCommitmentGens::new(&r1cs_size, b"gens_r1cs_eval");

    // create a commitment to R1CSInstance
    let (comm, decomm) = SpartanProof::encode(&inst, &gens_r1cs_eval);

    let gens_r1cs_sat = R1CSGens::new(num_cons, num_vars, b"gens_r1cs_sat");
    let gens = SpartanGens::new(gens_r1cs_sat, gens_r1cs_eval);

    let mut prover_transcript = Transcript::new(b"example");
    let proof = SpartanProof::prove(&inst, &decomm, vars, &input, &gens, &mut prover_transcript);

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&comm, &input, &mut verifier_transcript, &gens)
      .is_ok());
  }
}
