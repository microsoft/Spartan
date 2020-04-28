use super::dense_mlpoly::DensePolynomial;
use super::errors::ProofVerifyError;
use super::math::Math;
use super::random::RandomTape;
use super::scalar::Scalar;
use super::sparse_mlpoly::{
  MultiSparseMatPolynomialAsDense, SparseMatEntry, SparseMatPolyCommitment,
  SparseMatPolyCommitmentGens, SparseMatPolyEvalProof, SparseMatPolynomial,
  SparseMatPolynomialSize,
};
use super::timer::Timer;
use super::transcript::{AppendToTranscript, ProofTranscript};
use merlin::Transcript;
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

#[derive(Debug)]
pub struct R1CSInstance {
  num_cons: usize,
  num_vars: usize,
  num_inputs: usize,
  A: SparseMatPolynomial,
  B: SparseMatPolynomial,
  C: SparseMatPolynomial,
}

pub struct R1CSInstanceSize {
  size_A: SparseMatPolynomialSize,
  size_B: SparseMatPolynomialSize,
  size_C: SparseMatPolynomialSize,
}

pub struct R1CSCommitmentGens {
  gens: SparseMatPolyCommitmentGens,
}

impl R1CSCommitmentGens {
  pub fn new(size: &R1CSInstanceSize, label: &'static [u8]) -> R1CSCommitmentGens {
    assert_eq!(size.size_A, size.size_B);
    assert_eq!(size.size_A, size.size_C);
    let gens = SparseMatPolyCommitmentGens::new(&size.size_A, 3, label);
    R1CSCommitmentGens { gens }
  }
}

pub struct R1CSCommitment {
  num_cons: usize,
  num_vars: usize,
  num_inputs: usize,
  comm: SparseMatPolyCommitment,
}

pub struct R1CSDecommitment {
  dense: MultiSparseMatPolynomialAsDense,
}

impl R1CSCommitment {
  pub fn get_num_cons(&self) -> usize {
    self.num_cons
  }

  pub fn get_num_vars(&self) -> usize {
    self.num_vars
  }

  pub fn get_num_inputs(&self) -> usize {
    self.num_inputs
  }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct R1CSInstanceEvals {
  eval_A_r: Scalar,
  eval_B_r: Scalar,
  eval_C_r: Scalar,
}

impl R1CSInstanceEvals {
  pub fn get_evaluations(&self) -> (Scalar, Scalar, Scalar) {
    (self.eval_A_r, self.eval_B_r, self.eval_C_r)
  }
}

impl AppendToTranscript for R1CSInstanceEvals {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, b"R1CSInstanceEvals_begin");
    transcript.append_scalar(b"Ar_eval", &self.eval_A_r);
    transcript.append_scalar(b"Br_eval", &self.eval_B_r);
    transcript.append_scalar(b"Cr_eval", &self.eval_C_r);
    transcript.append_message(label, b"R1CSInstanceEvals_end");
  }
}

impl R1CSInstance {
  pub fn new(
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
    A: SparseMatPolynomial,
    B: SparseMatPolynomial,
    C: SparseMatPolynomial,
  ) -> Self {
    R1CSInstance {
      num_cons,
      num_vars,
      num_inputs,
      A,
      B,
      C,
    }
  }

  pub fn get_num_vars(&self) -> usize {
    self.num_vars
  }

  pub fn get_num_cons(&self) -> usize {
    self.num_cons
  }

  pub fn get_num_inputs(&self) -> usize {
    self.num_inputs
  }

  pub fn size(&self) -> R1CSInstanceSize {
    R1CSInstanceSize {
      size_A: self.A.size(),
      size_B: self.B.size(),
      size_C: self.C.size(),
    }
  }

  pub fn produce_synthetic_r1cs(
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
  ) -> (R1CSInstance, Vec<Scalar>, Vec<Scalar>) {
    let mut csprng: OsRng = OsRng;

    // assert num_cons and num_vars are power of 2
    assert_eq!(num_cons.log2().pow2(), num_cons);
    assert_eq!(num_vars.log2().pow2(), num_vars);

    // num_inputs + 1 <= num_vars
    assert!(num_inputs + 1 <= num_vars);

    // z is organized as [vars,1,io]
    let size_z = num_vars + num_inputs + 1;

    // produce a random satisfying assignment
    let Z = {
      let mut Z: Vec<Scalar> = (0..size_z)
        .map(|_i| Scalar::random(&mut csprng))
        .collect::<Vec<Scalar>>();
      Z[num_vars] = Scalar::one(); // set the constant term to 1
      Z
    };

    // three sparse matrices
    let mut A: Vec<SparseMatEntry> = Vec::new();
    let mut B: Vec<SparseMatEntry> = Vec::new();
    let mut C: Vec<SparseMatEntry> = Vec::new();
    let one = Scalar::one();
    for i in 0..num_cons {
      let A_idx = i % size_z;
      let B_idx = (i + 2) % size_z;
      A.push(SparseMatEntry::new(i, A_idx, one));
      B.push(SparseMatEntry::new(i, B_idx, one));
      let AB_val = Z[A_idx] * Z[B_idx];

      let C_idx = (i + 3) % size_z;
      let C_val = Z[C_idx];

      if C_val == Scalar::zero() {
        C.push(SparseMatEntry::new(i, num_vars, AB_val));
      } else {
        C.push(SparseMatEntry::new(
          i,
          C_idx,
          AB_val * C_val.invert().unwrap(),
        ));
      }
    }

    let num_poly_vars_x = num_cons.log2();
    let num_poly_vars_y = (2 * num_vars).log2();
    let poly_A = SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, A);
    let poly_B = SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, B);
    let poly_C = SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, C);

    let inst = R1CSInstance::new(num_cons, num_vars, num_inputs, poly_A, poly_B, poly_C);

    assert_eq!(
      inst.is_sat(&Z[0..num_vars].to_vec(), &Z[num_vars + 1..].to_vec()),
      true,
    );

    (inst, Z[0..num_vars].to_vec(), Z[num_vars + 1..].to_vec())
  }

  pub fn is_sat(&self, vars: &Vec<Scalar>, input: &Vec<Scalar>) -> bool {
    assert_eq!(vars.len(), self.num_vars);
    assert_eq!(input.len(), self.num_inputs);

    let z = {
      let mut z = vars.clone();
      z.extend(&vec![Scalar::one()]);
      z.extend(input);
      z
    };

    // verify if Az * Bz - Cz = [0...]
    let Az = self
      .A
      .multiply_vec(self.num_cons, self.num_vars + self.num_inputs + 1, &z);
    let Bz = self
      .B
      .multiply_vec(self.num_cons, self.num_vars + self.num_inputs + 1, &z);
    let Cz = self
      .C
      .multiply_vec(self.num_cons, self.num_vars + self.num_inputs + 1, &z);

    assert_eq!(Az.len(), self.num_cons);
    assert_eq!(Bz.len(), self.num_cons);
    assert_eq!(Cz.len(), self.num_cons);
    let res: usize = (0..self.num_cons)
      .map(|i| if Az[i] * Bz[i] == Cz[i] { 0 } else { 1 })
      .sum();
    if res > 0 {
      false
    } else {
      true
    }
  }

  pub fn multiply_vec(
    &self,
    num_rows: usize,
    num_cols: usize,
    z: &Vec<Scalar>,
  ) -> (DensePolynomial, DensePolynomial, DensePolynomial) {
    assert_eq!(num_rows, self.num_cons);
    assert_eq!(z.len(), num_cols);
    assert!(num_cols > self.num_vars);
    (
      DensePolynomial::new(self.A.multiply_vec(num_rows, num_cols, z)),
      DensePolynomial::new(self.B.multiply_vec(num_rows, num_cols, z)),
      DensePolynomial::new(self.C.multiply_vec(num_rows, num_cols, z)),
    )
  }

  pub fn compute_eval_table_sparse(
    &self,
    num_rows: usize,
    num_cols: usize,
    evals: &Vec<Scalar>,
  ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
    assert_eq!(num_rows, self.num_cons);
    assert!(num_cols > self.num_vars);

    let evals_A = self.A.compute_eval_table_sparse(&evals, num_rows, num_cols);
    let evals_B = self.B.compute_eval_table_sparse(&evals, num_rows, num_cols);
    let evals_C = self.C.compute_eval_table_sparse(&evals, num_rows, num_cols);

    (evals_A, evals_B, evals_C)
  }

  pub fn evaluate_with_tables(
    &self,
    evals_rx: &Vec<Scalar>,
    evals_ry: &Vec<Scalar>,
  ) -> R1CSInstanceEvals {
    R1CSInstanceEvals {
      eval_A_r: self.A.evaluate_with_tables(evals_rx, evals_ry),
      eval_B_r: self.B.evaluate_with_tables(evals_rx, evals_ry),
      eval_C_r: self.C.evaluate_with_tables(evals_rx, evals_ry),
    }
  }

  pub fn commit(&self, gens: &R1CSCommitmentGens) -> (R1CSCommitment, R1CSDecommitment) {
    assert_eq!(self.A.get_num_nz_entries(), self.B.get_num_nz_entries());
    assert_eq!(self.A.get_num_nz_entries(), self.C.get_num_nz_entries());
    let (comm, dense) =
      SparseMatPolynomial::multi_commit(&vec![&self.A, &self.B, &self.C], &gens.gens);
    let r1cs_comm = R1CSCommitment {
      num_cons: self.num_cons,
      num_vars: self.num_vars,
      num_inputs: self.num_inputs,
      comm,
    };

    let r1cs_decomm = R1CSDecommitment { dense };

    (r1cs_comm, r1cs_decomm)
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct R1CSEvalProof {
  proof: SparseMatPolyEvalProof,
}

impl R1CSEvalProof {
  pub fn prove(
    decomm: &R1CSDecommitment,
    rx: &Vec<Scalar>, // point at which the polynomial is evaluated
    ry: &Vec<Scalar>,
    evals: &R1CSInstanceEvals,
    gens: &R1CSCommitmentGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> R1CSEvalProof {
    let timer = Timer::new("R1CSEvalProof::prove");
    let proof = SparseMatPolyEvalProof::prove(
      &decomm.dense,
      rx,
      ry,
      &vec![evals.eval_A_r, evals.eval_B_r, evals.eval_C_r],
      &gens.gens,
      transcript,
      random_tape,
    );
    timer.stop();

    R1CSEvalProof { proof }
  }

  pub fn verify(
    &self,
    comm: &R1CSCommitment,
    rx: &Vec<Scalar>, // point at which the R1CS matrix polynomials are evaluated
    ry: &Vec<Scalar>,
    eval: &R1CSInstanceEvals,
    gens: &R1CSCommitmentGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    assert!(self
      .proof
      .verify(
        &comm.comm,
        rx,
        ry,
        &vec![eval.eval_A_r, eval.eval_B_r, eval.eval_C_r],
        &gens.gens,
        transcript
      )
      .is_ok());

    Ok(())
  }
}
