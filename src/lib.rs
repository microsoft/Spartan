#![allow(non_snake_case)]
#![feature(test)]
#![deny(missing_docs)]
#![feature(external_doc)]
#![doc(include = "../README.md")]

extern crate byteorder;
extern crate core;
extern crate curve25519_dalek;
extern crate digest;
extern crate merlin;
extern crate rand;
extern crate rayon;
extern crate sha3;
extern crate test;

mod commitments;
mod dense_mlpoly;
mod errors;
mod group;
mod math;
mod nizk;
mod product_tree;
mod r1csinstance;
mod r1csproof;
mod random;
mod scalar;
mod sparse_mlpoly;
mod sumcheck;
mod timer;
mod transcript;
mod unipoly;

use std::cmp::max;

use errors::{ProofVerifyError, R1CSError};
use merlin::Transcript;
use r1csinstance::{
  R1CSCommitment, R1CSCommitmentGens, R1CSDecommitment, R1CSEvalProof, R1CSInstance,
};
use r1csproof::{R1CSGens, R1CSProof};
use random::RandomTape;
use scalar::Scalar;
use serde::{Deserialize, Serialize};
use timer::Timer;
use transcript::{AppendToTranscript, ProofTranscript};

/// `ComputationCommitment` holds a public preprocessed NP statement (e.g., R1CS)
pub struct ComputationCommitment {
  comm: R1CSCommitment,
}

/// `ComputationDecommitment` holds information to decommit `ComputationCommitment`
pub struct ComputationDecommitment {
  decomm: R1CSDecommitment,
}

/// `Assignment` holds an assignment of values to either the inputs or variables in an `Instance`
#[derive(Clone)]
pub struct Assignment {
  assignment: Vec<Scalar>,
}

impl Assignment {
  /// Constructs a new `Assignment` from a vector
  pub fn new(assignment: &Vec<[u8; 32]>) -> Result<Assignment, R1CSError> {
    let bytes_to_scalar = |vec: &Vec<[u8; 32]>| -> Result<Vec<Scalar>, R1CSError> {
      let mut vec_scalar: Vec<Scalar> = Vec::new();
      for i in 0..vec.len() {
        let val = Scalar::from_bytes(&vec[i]);
        if val.is_some().unwrap_u8() == 1 {
          vec_scalar.push(val.unwrap());
        } else {
          return Err(R1CSError::InvalidScalar);
        }
      }
      Ok(vec_scalar)
    };

    let assignment_scalar = bytes_to_scalar(assignment);

    // check for any parsing errors
    if assignment_scalar.is_err() {
      return Err(R1CSError::InvalidScalar);
    }

    Ok(Assignment {
      assignment: assignment_scalar.unwrap(),
    })
  }
}

/// `VarsAssignment` holds an assignment of values to variables in an `Instance`
pub type VarsAssignment = Assignment;

/// `VarsAssignment` holds an assignment of values to variables in an `Instance`
pub type InputsAssignment = Assignment;

/// `Instance` holds the description of R1CS matrices
pub struct Instance {
  inst: R1CSInstance,
  vars_pad: usize
}

impl Instance {
  /// Constructs a new `Instance` and an associated satisfying assignment
  pub fn new(
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
    A: &Vec<(usize, usize, [u8; 32])>,
    B: &Vec<(usize, usize, [u8; 32])>,
    C: &Vec<(usize, usize, [u8; 32])>,
  ) -> Result<Instance, R1CSError> {

    let mut vars_pad = 0;
    let mut cons_pad = 0;

    // check that num_inputs + 1 <= num_vars
    if num_inputs >= num_vars {
      vars_pad = num_inputs - num_vars + 1;
    }

    // check that num_cons is power of 2
    if num_cons.next_power_of_two() != num_cons {
      cons_pad = num_cons.next_power_of_two() - num_cons;
    }

    if num_cons.next_power_of_two() < 2 {
      cons_pad = 2-num_cons.next_power_of_two();
    }

    // check that the number of variables is a power of 2
    if num_vars.next_power_of_two() != num_vars + vars_pad {
      vars_pad = max(num_vars.next_power_of_two() - num_vars, vars_pad);
    }

    let bytes_to_scalar =
      |tups: &Vec<(usize, usize, [u8; 32])>| -> Result<Vec<(usize, usize, Scalar)>, R1CSError> {
        let mut mat: Vec<(usize, usize, Scalar)> = Vec::new();
        for i in 0..tups.len() {
          let (row, col, val_bytes) = tups[i];

          // row must be smaller than num_cons
          if row >= num_cons {
            return Err(R1CSError::InvalidIndex);
          }

          // col must be smaller than num_vars + 1 + num_inputs
          if col >= num_vars + 1 + num_inputs {
            return Err(R1CSError::InvalidIndex);
          }

          let val = Scalar::from_bytes(&val_bytes);
          if val.is_some().unwrap_u8() == 1 {
            mat.push((row, col, val.unwrap()));
          } else {
            return Err(R1CSError::InvalidScalar);
          }
        }

        // Pad with additional constraints up until a power of 2
        for i in tups.len()..(num_cons + cons_pad) {
          mat.push((i, num_vars, Scalar::zero()));
        }
        Ok(mat)
      };

    let A_scalar = bytes_to_scalar(A);
    if A_scalar.is_err() {
      return Err(A_scalar.err().unwrap());
    }

    let B_scalar = bytes_to_scalar(B);
    if B_scalar.is_err() {
      return Err(B_scalar.err().unwrap());
    }

    let C_scalar = bytes_to_scalar(C);
    if C_scalar.is_err() {
      return Err(C_scalar.err().unwrap());
    }

    let inst = R1CSInstance::new(
      num_cons + cons_pad,
      num_vars + vars_pad,
      num_inputs,
      &A_scalar.unwrap(),
      &B_scalar.unwrap(),
      &C_scalar.unwrap(),
    );

    Ok(Instance { inst, vars_pad })
  }

  // Work for any number of variables
  fn pad_variables(&self, vars: &Vec<Scalar>) -> Vec<Scalar> {
      let mut padding = vec![Scalar::zero(); self.vars_pad];
      let mut padded_assignment = vars.clone();
      padded_assignment.append(&mut padding);
      padded_assignment
  }

  /// Checks if a given R1CSInstance is satisfiable with a given variables and inputs assignments
  pub fn is_sat(
    &self,
    vars: &VarsAssignment,
    inputs: &InputsAssignment,
  ) -> Result<bool, R1CSError> {
    if vars.assignment.len() + self.vars_pad != self.inst.get_num_vars() {
      return Err(R1CSError::InvalidNumberOfVars);
    }

    if inputs.assignment.len() != self.inst.get_num_inputs() {
      return Err(R1CSError::InvalidNumberOfInputs);
    }

    // Might need to create dummy variables
    if self.vars_pad > 0 {
      Ok(self.inst.is_sat(&self.pad_variables(&vars.assignment), &inputs.assignment))
    } else {
      Ok(self.inst.is_sat(&vars.assignment, &inputs.assignment))
    }
  }

  /// Constructs a new synthetic R1CS `Instance` and an associated satisfying assignment
  pub fn produce_synthetic_r1cs(
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
  ) -> (Instance, VarsAssignment, InputsAssignment) {
    let (inst, vars, inputs) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    (
      Instance { inst, vars_pad: 0 },
      VarsAssignment { assignment: vars },
      InputsAssignment { assignment: inputs },
    )
  }
}

/// `SNARKGens` holds public parameters for producing and verifying proofs with the Spartan SNARK
pub struct SNARKGens {
  gens_r1cs_sat: R1CSGens,
  gens_r1cs_eval: R1CSCommitmentGens,
}

impl SNARKGens {
  /// Constructs a new `SNARKGens` given the size of the R1CS statement
  pub fn new(num_cons: usize, num_vars: usize, num_inputs: usize, num_nz_entries: usize) -> Self {
    let mut vars_pad = 0;
    if num_inputs >= num_vars {
      vars_pad = num_inputs - num_vars + 1;
    }
    let gens_r1cs_sat = R1CSGens::new(b"gens_r1cs_sat", num_cons, num_vars + vars_pad);
    let gens_r1cs_eval = R1CSCommitmentGens::new(
      b"gens_r1cs_eval",
      num_cons,
      num_vars + vars_pad,
      num_inputs,
      num_nz_entries,
    );
    SNARKGens {
      gens_r1cs_sat,
      gens_r1cs_eval,
    }
  }
}

/// `SNARK` holds a proof produced by Spartan SNARK
#[derive(Serialize, Deserialize, Debug)]
pub struct SNARK {
  r1cs_sat_proof: R1CSProof,
  inst_evals: (Scalar, Scalar, Scalar),
  r1cs_eval_proof: R1CSEvalProof,
}

impl SNARK {
  fn protocol_name() -> &'static [u8] {
    b"Spartan SNARK proof"
  }

  /// A public computation to create a commitment to an R1CS instance
  pub fn encode(
    inst: &Instance,
    gens: &SNARKGens,
  ) -> (ComputationCommitment, ComputationDecommitment) {
    let timer_encode = Timer::new("SNARK::encode");
    let (comm, decomm) = inst.inst.commit(&gens.gens_r1cs_eval);
    timer_encode.stop();
    (
      ComputationCommitment { comm },
      ComputationDecommitment { decomm },
    )
  }

  /// A method to produce a SNARK proof of the satisfiability of an R1CS instance
  pub fn prove(
    inst: &Instance,
    decomm: &ComputationDecommitment,
    vars: VarsAssignment,
    inputs: &InputsAssignment,
    gens: &SNARKGens,
    transcript: &mut Transcript,
  ) -> Self {
    let timer_prove = Timer::new("SNARK::prove");

    // we create a Transcript object seeded with a random Scalar
    // to aid the prover produce its randomness
    let mut random_tape = RandomTape::new(b"proof");
    transcript.append_protocol_name(SNARK::protocol_name());
    let (r1cs_sat_proof, rx, ry) = {
      let (proof, rx, ry) =
          // Might need to create dummy variables
          R1CSProof::prove(
            &inst.inst,
            if inst.vars_pad > 0 { inst.pad_variables(&vars.assignment) } else { vars.assignment },
            &inputs.assignment,
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
      let (Ar, Br, Cr) = inst.inst.evaluate(&rx, &ry);
      Ar.append_to_transcript(b"Ar_claim", transcript);
      Br.append_to_transcript(b"Br_claim", transcript);
      Cr.append_to_transcript(b"Cr_claim", transcript);
      (Ar, Br, Cr)
    };
    timer_eval.stop();

    let r1cs_eval_proof = {
      let proof = R1CSEvalProof::prove(
        &decomm.decomm,
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

    timer_prove.stop();
    SNARK {
      r1cs_sat_proof,
      inst_evals,
      r1cs_eval_proof,
    }
  }

  /// A method to verify the SNARK proof of the satisfiability of an R1CS instance
  pub fn verify(
    &self,
    comm: &ComputationCommitment,
    input: &InputsAssignment,
    transcript: &mut Transcript,
    gens: &SNARKGens,
  ) -> Result<(), ProofVerifyError> {
    let timer_verify = Timer::new("SNARK::verify");
    transcript.append_protocol_name(SNARK::protocol_name());

    let timer_sat_proof = Timer::new("verify_sat_proof");
    assert_eq!(input.assignment.len(), comm.comm.get_num_inputs());
    let (rx, ry) = self.r1cs_sat_proof.verify(
      comm.comm.get_num_vars(),
      comm.comm.get_num_cons(),
      &input.assignment,
      &self.inst_evals,
      transcript,
      &gens.gens_r1cs_sat,
    )?;
    timer_sat_proof.stop();

    let timer_eval_proof = Timer::new("verify_eval_proof");
    let (Ar, Br, Cr) = &self.inst_evals;
    Ar.append_to_transcript(b"Ar_claim", transcript);
    Br.append_to_transcript(b"Br_claim", transcript);
    Cr.append_to_transcript(b"Cr_claim", transcript);
    assert!(self
      .r1cs_eval_proof
      .verify(
        &comm.comm,
        &rx,
        &ry,
        &self.inst_evals,
        &gens.gens_r1cs_eval,
        transcript
      )
      .is_ok());
    timer_eval_proof.stop();
    timer_verify.stop();
    Ok(())
  }
}

/// `NIZKGens` holds public parameters for producing and verifying proofs with the Spartan NIZK
pub struct NIZKGens {
  gens_r1cs_sat: R1CSGens,
}

impl NIZKGens {
  /// Constructs a new `NIZKGens` given the size of the R1CS statement
  pub fn new(num_cons: usize, num_vars: usize) -> Self {
    let gens_r1cs_sat = R1CSGens::new(b"gens_r1cs_sat", num_cons, num_vars);
    NIZKGens { gens_r1cs_sat }
  }
}

/// `NIZK` holds a proof produced by Spartan NIZK
#[derive(Serialize, Deserialize, Debug)]
pub struct NIZK {
  r1cs_sat_proof: R1CSProof,
  r: (Vec<Scalar>, Vec<Scalar>),
}

impl NIZK {
  fn protocol_name() -> &'static [u8] {
    b"Spartan NIZK proof"
  }

  /// A method to produce a NIZK proof of the satisfiability of an R1CS instance
  pub fn prove(
    inst: &Instance,
    vars: VarsAssignment,
    input: &InputsAssignment,
    gens: &NIZKGens,
    transcript: &mut Transcript,
  ) -> Self {
    let timer_prove = Timer::new("NIZK::prove");
    // we create a Transcript object seeded with a random Scalar
    // to aid the prover produce its randomness
    let mut random_tape = RandomTape::new(b"proof");
    transcript.append_protocol_name(NIZK::protocol_name());
    let (r1cs_sat_proof, rx, ry) = {
      let (proof, rx, ry) = R1CSProof::prove(
        &inst.inst,
        vars.assignment,
        &input.assignment,
        &gens.gens_r1cs_sat,
        transcript,
        &mut random_tape,
      );
      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));
      (proof, rx, ry)
    };

    timer_prove.stop();
    NIZK {
      r1cs_sat_proof,
      r: (rx, ry),
    }
  }

  /// A method to verify a NIZK proof of the satisfiability of an R1CS instance
  pub fn verify(
    &self,
    inst: &Instance,
    input: &InputsAssignment,
    transcript: &mut Transcript,
    gens: &NIZKGens,
  ) -> Result<(), ProofVerifyError> {
    let timer_verify = Timer::new("NIZK::verify");

    transcript.append_protocol_name(NIZK::protocol_name());

    // We send evaluations of A, B, C at r = (rx, ry) as claims
    // to enable the verifier complete the first sum-check
    let timer_eval = Timer::new("eval_sparse_polys");
    let (claimed_rx, claimed_ry) = &self.r;
    let inst_evals = inst.inst.evaluate(claimed_rx, claimed_ry);
    timer_eval.stop();

    let timer_sat_proof = Timer::new("verify_sat_proof");
    assert_eq!(input.assignment.len(), inst.inst.get_num_inputs());
    let (rx, ry) = self.r1cs_sat_proof.verify(
      inst.inst.get_num_vars(),
      inst.inst.get_num_cons(),
      &input.assignment,
      &inst_evals,
      transcript,
      &gens.gens_r1cs_sat,
    )?;

    // verify if claimed rx and ry are correct
    assert_eq!(rx, *claimed_rx);
    assert_eq!(ry, *claimed_ry);
    timer_sat_proof.stop();
    timer_verify.stop();

    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  pub fn check_snark() {
    let num_vars = 256;
    let num_cons = num_vars;
    let num_inputs = 10;

    // produce public generators
    let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_cons);

    // produce a synthetic R1CSInstance
    let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    // create a commitment to R1CSInstance
    let (comm, decomm) = SNARK::encode(&inst, &gens);

    // produce a proof
    let mut prover_transcript = Transcript::new(b"example");
    let proof = SNARK::prove(&inst, &decomm, vars, &inputs, &gens, &mut prover_transcript);

    // verify the proof
    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&comm, &inputs, &mut verifier_transcript, &gens)
      .is_ok());
  }

  #[test]
  pub fn check_r1cs_invalid_index() {
    let num_cons = 4;
    let num_vars = 8;
    let num_inputs = 1;

    let zero: [u8; 32] = [
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0,
    ];

    let A = vec![(0, 0, zero)];
    let B = vec![(100, 1, zero)];
    let C = vec![(1, 1, zero)];

    let inst = Instance::new(num_cons, num_vars, num_inputs, &A, &B, &C);
    assert_eq!(inst.is_err(), true);
    assert_eq!(inst.err(), Some(R1CSError::InvalidIndex));
  }

  #[test]
  pub fn check_r1cs_invalid_scalar() {
    let num_cons = 4;
    let num_vars = 8;
    let num_inputs = 1;

    let zero: [u8; 32] = [
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0,
    ];

    let larger_than_mod = [
      3, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8, 216,
      57, 51, 72, 125, 157, 41, 83, 167, 237, 115,
    ];

    let A = vec![(0, 0, zero)];
    let B = vec![(1, 1, larger_than_mod)];
    let C = vec![(1, 1, zero)];

    let inst = Instance::new(num_cons, num_vars, num_inputs, &A, &B, &C);
    assert_eq!(inst.is_err(), true);
    assert_eq!(inst.err(), Some(R1CSError::InvalidScalar));
  }
}
