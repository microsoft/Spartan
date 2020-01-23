#[allow(dead_code)]
use super::dense_mlpoly::DensePolynomial;
use super::dense_mlpoly::{
  DensePolynomialSize, EqPolynomial, IdentityPolynomial, PolyCommitment, PolyCommitmentGens,
  PolyEvalProof,
};
use super::errors::ProofVerifyError;
use super::math::Math;
use super::product_tree::{DotProductCircuit, ProductCircuit, ProductCircuitEvalProofBatched};
use super::scalar::Scalar;
use super::transcript::{AppendToTranscript, ProofTranscript};
use merlin::Transcript;
use serde::{Deserialize, Serialize};
use std::time::Instant;

#[derive(Debug)]
pub struct SparseMatEntry {
  row: usize,
  col: usize,
  val: Scalar,
}

impl SparseMatEntry {
  pub fn new(row: usize, col: usize, val: Scalar) -> Self {
    SparseMatEntry { row, col, val }
  }
}

#[derive(Debug)]
pub struct SparseMatPolynomial {
  num_vars_x: usize,
  num_vars_y: usize,
  M: Vec<SparseMatEntry>,
}

struct AddrTimestamps {
  ops_addr_usize: Vec<usize>,
  ops_addr: DensePolynomial,
  read_ts: DensePolynomial,
  audit_ts: DensePolynomial,
}

pub struct Derefs {
  row_ops_val: DensePolynomial,
  col_ops_val: DensePolynomial,
  ops_val: DensePolynomial,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DerefsCommitment {
  comm_ops_val: PolyCommitment,
}

impl Derefs {
  pub fn new(row_ops_val: DensePolynomial, col_ops_val: DensePolynomial) -> Self {
    // combine the two polynomials into a single polynomial (used below to produce a single commitment)
    let mut ops_val = row_ops_val.clone();
    ops_val.extend(&col_ops_val);
    Derefs {
      row_ops_val,
      col_ops_val,
      ops_val,
    }
  }

  pub fn commit(&self, gens: &PolyCommitmentGens) -> DerefsCommitment {
    let blinds = None;
    let comm_ops_val = self.ops_val.commit(blinds, gens);
    DerefsCommitment { comm_ops_val }
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DerefsEvalProof {
  proof_derefs: PolyEvalProof,
}

impl DerefsEvalProof {
  fn protocol_name() -> &'static [u8] {
    b"Derefs evaluation proof"
  }

  // evalues both polynomials at r and produces a joint proof of opening
  pub fn prove(
    derefs: &Derefs,
    eval_row_ops_val: &Scalar,
    eval_col_ops_val: &Scalar,
    r: &Vec<Scalar>,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
  ) -> Self {
    transcript.append_protocol_name(DerefsEvalProof::protocol_name());

    // append the claimed evaluations to transcript
    eval_row_ops_val.append_to_transcript(b"eval_row_ops_val", transcript);
    eval_col_ops_val.append_to_transcript(b"eval_col_ops_val", transcript);

    // 2-to-1 reduction
    let challenge = transcript.challenge_scalar(b"challenge_combine_two_to_one");
    let joint_claim_eval = eval_row_ops_val + &challenge * (eval_col_ops_val - eval_row_ops_val);
    let mut r_joint = vec![challenge];
    r_joint.extend(r);

    // decommit the joint polynomial at r_joint
    joint_claim_eval.append_to_transcript(b"joint_claim_eval", transcript);
    let (proof_derefs, _comm_derefs_eval) = PolyEvalProof::prove(
      &derefs.ops_val,
      None,
      &r_joint,
      &joint_claim_eval,
      None,
      gens,
      transcript,
    );

    DerefsEvalProof { proof_derefs }
  }

  // verify evaluations of both polynomials at r
  pub fn verify(
    &self,
    r: &Vec<Scalar>,
    eval_row_ops_val: &Scalar,
    eval_col_ops_val: &Scalar,
    gens: &PolyCommitmentGens,
    comm: &DerefsCommitment,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(DerefsEvalProof::protocol_name());

    // append the claimed evaluations to transcript
    eval_row_ops_val.append_to_transcript(b"eval_row_ops_val", transcript);
    eval_col_ops_val.append_to_transcript(b"eval_col_ops_val", transcript);

    // 2-to-1 reduction
    let challenge = transcript.challenge_scalar(b"challenge_combine_two_to_one");
    let joint_claim_eval = eval_row_ops_val + &challenge * (eval_col_ops_val - eval_row_ops_val);
    let mut r_joint = vec![challenge];
    r_joint.extend(r);

    // decommit the joint polynomial at r_joint
    joint_claim_eval.append_to_transcript(b"joint_claim_eval", transcript);
    assert!(self
      .proof_derefs
      .verify_plain(
        gens,
        transcript,
        &r_joint,
        &joint_claim_eval,
        &comm.comm_ops_val
      )
      .is_ok());

    Ok(())
  }
}

impl AppendToTranscript for DerefsCommitment {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(b"derefs_commitment", b"begin_derefs_commitment");
    self.comm_ops_val.append_to_transcript(label, transcript);
    transcript.append_message(b"derefs_commitment", b"end_derefs_commitment");
  }
}

#[derive(Debug, Serialize, Deserialize)]
struct AddrTimestampsCommitment {
  ops_addr: PolyCommitment,
  read_ts: PolyCommitment,
  audit_ts: PolyCommitment,
}

impl AddrTimestamps {
  pub fn new(num_cells: usize, ops_addr: Vec<usize>) -> Self {
    let num_ops = ops_addr.len();

    let mut read_ts = vec![0usize; num_ops];
    let mut audit_ts = vec![0usize; num_cells];

    // since read timestamps are trustworthy, we can simply increment the r-ts to obtain a w-ts
    // this is sufficient to ensure that the write-set, consisting of (addr, val, ts) tuples, is a set
    for i in 0..num_ops {
      let addr = ops_addr[i];
      assert!(addr < num_cells);
      let r_ts = audit_ts[addr];
      read_ts[i] = r_ts;

      let w_ts = r_ts + 1;
      audit_ts[addr] = w_ts;
    }

    AddrTimestamps {
      ops_addr: DensePolynomial::from_usize(&ops_addr),
      ops_addr_usize: ops_addr,
      read_ts: DensePolynomial::from_usize(&read_ts),
      audit_ts: DensePolynomial::from_usize(&audit_ts),
    }
  }

  pub fn commit(
    &self,
    gens_ops: &PolyCommitmentGens,
    gens_mem: &PolyCommitmentGens,
  ) -> AddrTimestampsCommitment {
    let blinds = None;

    AddrTimestampsCommitment {
      ops_addr: self.ops_addr.commit(blinds, gens_ops),
      read_ts: self.read_ts.commit(blinds, gens_ops),
      audit_ts: self.audit_ts.commit(blinds, gens_mem),
    }
  }

  pub fn deref(&self, mem_val: &Vec<Scalar>) -> DensePolynomial {
    DensePolynomial::new(
      (0..self.ops_addr.len())
        .map(|i| {
          let addr = self.ops_addr_usize[i];
          mem_val[addr]
        })
        .collect::<Vec<Scalar>>(),
    )
  }
}

pub struct SparseMatPolynomialAsDense {
  val: DensePolynomial,
  row: AddrTimestamps,
  col: AddrTimestamps,
}

pub struct SparseMatPolynomialSize {
  size_ops: DensePolynomialSize,
  size_mem: DensePolynomialSize,
  size_derefs: DensePolynomialSize,
}

pub struct SparseMatPolyCommitmentGens {
  gens_ops: PolyCommitmentGens,
  gens_mem: PolyCommitmentGens,
  gens_derefs: PolyCommitmentGens,
}

impl SparseMatPolyCommitmentGens {
  pub fn new(size: &SparseMatPolynomialSize, label: &'static [u8]) -> SparseMatPolyCommitmentGens {
    let gens_ops = PolyCommitmentGens::new(&size.size_ops, label);
    let gens_mem = PolyCommitmentGens::new(&size.size_mem, label);
    let gens_derefs = PolyCommitmentGens::new(&size.size_derefs, label);
    SparseMatPolyCommitmentGens {
      gens_ops,
      gens_mem,
      gens_derefs,
    }
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SparseMatPolyCommitment {
  comm_row: AddrTimestampsCommitment,
  comm_col: AddrTimestampsCommitment,
  comm_val: PolyCommitment,
}

impl SparseMatPolynomial {
  pub fn new(num_vars_x: usize, num_vars_y: usize, M: Vec<SparseMatEntry>) -> Self {
    SparseMatPolynomial {
      num_vars_x,
      num_vars_y,
      M,
    }
  }

  pub fn get_num_nz_entries(&self) -> usize {
    self.M.len().next_power_of_two()
  }

  fn sparse_to_dense_rep(&self) -> SparseMatPolynomialAsDense {
    let N = self.get_num_nz_entries();
    let mut ops_row: Vec<usize> = vec![0; N];
    let mut ops_col: Vec<usize> = vec![0; N];
    let mut val: Vec<Scalar> = vec![Scalar::zero(); N];

    for i in 0..self.M.len() {
      ops_row[i] = self.M[i].row;
      ops_col[i] = self.M[i].col;
      val[i] = self.M[i].val;
    }

    let num_mem_cells = if self.num_vars_x > self.num_vars_y {
      self.num_vars_x.pow2()
    } else {
      self.num_vars_y.pow2()
    };

    let row = AddrTimestamps::new(num_mem_cells, ops_row);
    let col = AddrTimestamps::new(num_mem_cells, ops_col);

    SparseMatPolynomialAsDense {
      row,
      col,
      val: DensePolynomial::new(val),
    }
  }

  pub fn size(&self) -> SparseMatPolynomialSize {
    let dense = self.sparse_to_dense_rep();

    assert_eq!(dense.col.audit_ts.len(), dense.row.audit_ts.len());
    SparseMatPolynomialSize {
      size_mem: DensePolynomialSize::new(dense.row.audit_ts.get_num_vars()),
      size_ops: DensePolynomialSize::new(dense.row.read_ts.get_num_vars()),
      size_derefs: DensePolynomialSize::new(dense.row.read_ts.get_num_vars() + 1),
    }
  }

  pub fn evaluate_with_tables(
    &self,
    eval_table_rx: &Vec<Scalar>,
    eval_table_ry: &Vec<Scalar>,
  ) -> Scalar {
    assert_eq!(self.num_vars_x.pow2(), eval_table_rx.len());
    assert_eq!(self.num_vars_y.pow2(), eval_table_ry.len());

    (0..self.M.len())
      .map(|i| {
        let row = self.M[i].row;
        let col = self.M[i].col;
        let val = &self.M[i].val;
        &eval_table_rx[row] * &eval_table_ry[col] * val
      })
      .sum()
  }

  pub fn evaluate(&self, rx: &Vec<Scalar>, ry: &Vec<Scalar>) -> Scalar {
    let eval_table_rx = EqPolynomial::new(rx.clone()).evals();
    let eval_table_ry = EqPolynomial::new(ry.clone()).evals();
    assert_eq!(self.num_vars_x.pow2(), eval_table_rx.len());
    assert_eq!(self.num_vars_y.pow2(), eval_table_ry.len());

    (0..self.M.len())
      .map(|i| {
        let row = self.M[i].row;
        let col = self.M[i].col;
        let val = &self.M[i].val;
        &eval_table_rx[row] * &eval_table_ry[col] * val
      })
      .sum()
  }

  pub fn multiply_vec(&self, num_rows: usize, num_cols: usize, z: &Vec<Scalar>) -> Vec<Scalar> {
    assert_eq!(z.len(), num_cols);

    (0..self.M.len())
      .map(|i| {
        let row = self.M[i].row;
        let col = self.M[i].col;
        let val = &self.M[i].val;
        (row, val * z[col])
      })
      .fold(vec![Scalar::zero(); num_rows], |mut Mz, (r, v)| {
        Mz[r] += v;
        Mz
      })
  }

  pub fn compute_eval_table_sparse(
    &self,
    rx: &Vec<Scalar>,
    num_rows: usize,
    num_cols: usize,
  ) -> Vec<Scalar> {
    assert_eq!(rx.len(), num_rows);

    let mut M_evals: Vec<Scalar> = vec![Scalar::zero(); num_cols];

    for i in 0..self.M.len() {
      let entry = &self.M[i];
      M_evals[entry.col] += rx[entry.row] * entry.val;
    }
    M_evals
  }

  pub fn commit(
    &self,
    gens: &SparseMatPolyCommitmentGens,
  ) -> (SparseMatPolyCommitment, SparseMatPolynomialAsDense) {
    let dense = self.sparse_to_dense_rep();
    let comm_row = dense.row.commit(&gens.gens_ops, &gens.gens_mem);
    let comm_col = dense.col.commit(&gens.gens_ops, &gens.gens_mem);
    let comm_val = dense.val.commit(None, &gens.gens_ops);
    (
      SparseMatPolyCommitment {
        comm_row,
        comm_col,
        comm_val,
      },
      dense,
    )
  }
}

impl SparseMatPolynomialAsDense {
  pub fn deref(&self, row_mem_val: &Vec<Scalar>, col_mem_val: &Vec<Scalar>) -> Derefs {
    let row_ops_val = self.row.deref(row_mem_val);
    let col_ops_val = self.col.deref(col_mem_val);

    Derefs::new(row_ops_val, col_ops_val)
  }
}

#[derive(Debug)]
struct MemCircuitHashLayer {
  init: DensePolynomial,
  read: DensePolynomial,
  write: DensePolynomial,
  audit: DensePolynomial,
}

#[derive(Debug)]
struct MemCircuitProductLayer {
  init: ProductCircuit,
  read: ProductCircuit,
  write: ProductCircuit,
  audit: ProductCircuit,
}

#[derive(Debug)]
struct MemCircuitLayers {
  hash_layer: MemCircuitHashLayer,
  prod_layer: MemCircuitProductLayer,
}

impl MemCircuitLayers {
  fn build_hash_layer(
    r_hash: &Scalar,
    eval_table: &Vec<Scalar>,
    addrs: &DensePolynomial,
    derefs: &DensePolynomial,
    read_ts: &DensePolynomial,
    audit_ts: &DensePolynomial,
    r_multiset_check: &Scalar,
  ) -> (
    DensePolynomial,
    DensePolynomial,
    DensePolynomial,
    DensePolynomial,
  ) {
    //hash(addr, val, ts) = ts * r_hash_sqr + val * r_hash + addr
    let r_hash_sqr = r_hash * r_hash;
    let hash_func = |addr: &Scalar, val: &Scalar, ts: &Scalar| -> Scalar {
      ts * &r_hash_sqr + val * r_hash + addr
    };

    let num_mem_cells = eval_table.len();
    let num_ops = addrs.len();

    let poly_init_hashed = DensePolynomial::new(
      (0..num_mem_cells)
        .map(|i| {
          // at init time, addr is given by i, init value is given by eval_table, and ts = 0
          &hash_func(&Scalar::from(i as u64), &eval_table[i], &Scalar::zero()) - r_multiset_check
        })
        .collect::<Vec<Scalar>>(),
    );

    let poly_read_hashed = DensePolynomial::new(
      (0..num_ops)
        .map(|i| {
          // at read time, addr is given by addrs, value is given by derefs, and ts is given by read_ts
          &hash_func(&addrs[i], &derefs[i], &read_ts[i]) - r_multiset_check
        })
        .collect::<Vec<Scalar>>(),
    );

    let poly_write_hashed = DensePolynomial::new(
      (0..num_ops)
        .map(|i| {
          // at write time, addr is given by addrs, value is given by derefs, and ts is given by write_ts = read_ts + 1
          &hash_func(&addrs[i], &derefs[i], &(&read_ts[i] + &Scalar::one())) - r_multiset_check
        })
        .collect::<Vec<Scalar>>(),
    );

    let poly_audit_hashed = DensePolynomial::new(
      (0..num_mem_cells)
        .map(|i| {
          // at audit time, addr is given by i, value is given by eval_table, and ts is given by audit_ts
          &hash_func(&Scalar::from(i as u64), &eval_table[i], &audit_ts[i]) - r_multiset_check
        })
        .collect::<Vec<Scalar>>(),
    );

    (
      poly_init_hashed,
      poly_read_hashed,
      poly_write_hashed,
      poly_audit_hashed,
    )
  }

  pub fn new(
    mem_ops_val: &Vec<Scalar>,
    addr_timestamps: &AddrTimestamps,
    poly_ops_val: &DensePolynomial,
    r_hash: &Scalar,
    r_multiset_check: &Scalar,
  ) -> Self {
    let (poly_init_hashed, poly_read_hashed, poly_write_hashed, poly_audit_hashed) =
      MemCircuitLayers::build_hash_layer(
        &r_hash,
        mem_ops_val,
        &addr_timestamps.ops_addr,
        &poly_ops_val,
        &addr_timestamps.read_ts,
        &addr_timestamps.audit_ts,
        &r_multiset_check,
      );

    assert_eq!(
      poly_init_hashed.get_num_vars(),
      poly_audit_hashed.get_num_vars()
    );
    assert_eq!(
      poly_read_hashed.get_num_vars(),
      poly_write_hashed.get_num_vars()
    );

    assert_eq!(poly_init_hashed.get_num_vars(), mem_ops_val.len().log2());
    assert_eq!(
      poly_read_hashed.get_num_vars(),
      addr_timestamps.ops_addr.get_num_vars()
    );

    let prod_init = ProductCircuit::new(&poly_init_hashed);
    let prod_read = ProductCircuit::new(&poly_read_hashed);
    let prod_write = ProductCircuit::new(&poly_write_hashed);
    let prod_audit = ProductCircuit::new(&poly_audit_hashed);

    // subset audit check
    assert_eq!(
      prod_init.evaluate() * prod_write.evaluate(),
      prod_read.evaluate() * prod_audit.evaluate()
    );

    MemCircuitLayers {
      prod_layer: MemCircuitProductLayer {
        init: prod_init,
        read: prod_read,
        write: prod_write,
        audit: prod_audit,
      },

      hash_layer: MemCircuitHashLayer {
        init: poly_init_hashed,
        read: poly_read_hashed,
        write: poly_write_hashed,
        audit: poly_audit_hashed,
      },
    }
  }
}

#[derive(Debug)]
struct MemCircuit {
  row_layers: MemCircuitLayers,
  col_layers: MemCircuitLayers,
}

impl MemCircuit {
  pub fn new(
    eval_table_rx: &Vec<Scalar>,
    eval_table_ry: &Vec<Scalar>,
    derefs: &Derefs,
    dense: &SparseMatPolynomialAsDense,
    r_hash: &Scalar,
    r_multiset_check: &Scalar,
  ) -> MemCircuit {
    let row_layers = MemCircuitLayers::new(
      eval_table_rx,
      &dense.row,
      &derefs.row_ops_val,
      r_hash,
      r_multiset_check,
    );
    let col_layers = MemCircuitLayers::new(
      eval_table_ry,
      &dense.col,
      &derefs.col_ops_val,
      r_hash,
      r_multiset_check,
    );

    MemCircuit {
      row_layers,
      col_layers,
    }
  }
}

#[derive(Debug)]
struct PolyEvalNetwork {
  r: (Vec<Scalar>, Vec<Scalar>),
  mem_circuit: MemCircuit,
}

impl PolyEvalNetwork {
  pub fn new(
    dense: &SparseMatPolynomialAsDense,
    derefs: &Derefs,
    rx: &Vec<Scalar>,
    ry: &Vec<Scalar>,
    eval_table_rx: &Vec<Scalar>,
    eval_table_ry: &Vec<Scalar>,
    r_hash: &Scalar,
    r_multiset_check: &Scalar,
  ) -> Self {
    assert_eq!(rx.len().pow2(), eval_table_rx.len());
    assert_eq!(ry.len().pow2(), eval_table_ry.len());

    // build memory checking circuit
    let mem_circuit = MemCircuit::new(
      eval_table_rx,
      eval_table_ry,
      derefs,
      &dense,
      &r_hash,
      &r_multiset_check,
    );

    PolyEvalNetwork {
      r: (rx.to_vec(), ry.to_vec()),
      mem_circuit,
    }
  }
}

#[derive(Debug, Serialize, Deserialize)]
struct HashLayerProof {
  eval_row: (Scalar, Scalar, Scalar),
  proof_row: (PolyEvalProof, PolyEvalProof, PolyEvalProof),
  eval_col: (Scalar, Scalar, Scalar),
  proof_col: (PolyEvalProof, PolyEvalProof, PolyEvalProof),
  eval_derefs: (Scalar, Scalar),
  proof_derefs: DerefsEvalProof,
  eval_val: Scalar,
  proof_val: PolyEvalProof,
}

impl HashLayerProof {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial hash layer proof"
  }

  fn prove_helper(
    rand: (&Vec<Scalar>, &Vec<Scalar>),
    addr_timestamps: &AddrTimestamps,
    gens_mem: &PolyCommitmentGens,
    gens_ops: &PolyCommitmentGens,
    transcript: &mut Transcript,
  ) -> (
    (Scalar, Scalar, Scalar),
    (PolyEvalProof, PolyEvalProof, PolyEvalProof),
  ) {
    let (rand_mem, rand_ops) = rand;

    // decommit read-ts, write-ts, ops-addr, and ops-val at rand_ops
    let eval_ops_addr = addr_timestamps.ops_addr.evaluate(rand_ops);
    eval_ops_addr.append_to_transcript(b"claim_eval_ops_addr", transcript);
    let (proof_ops_addr, _comm_ops_addr_eval) = PolyEvalProof::prove(
      &addr_timestamps.ops_addr,
      None,
      &rand_ops,
      &eval_ops_addr,
      None,
      gens_ops,
      transcript,
    );

    let eval_read_ts = addr_timestamps.read_ts.evaluate(rand_ops);
    eval_read_ts.append_to_transcript(b"claim_eval_read_ts", transcript);
    let (proof_read_ts, _comm_read_ts_eval) = PolyEvalProof::prove(
      &addr_timestamps.read_ts,
      None,
      &rand_ops,
      &eval_read_ts,
      None,
      gens_ops,
      transcript,
    );

    // decommit audit-ts at rand_mem
    let eval_audit_ts = addr_timestamps.audit_ts.evaluate(rand_mem);
    eval_audit_ts.append_to_transcript(b"claim_eval_audit_ts", transcript);
    let (proof_audit_ts, _comm_audit_ts_eval) = PolyEvalProof::prove(
      &addr_timestamps.audit_ts,
      None,
      &rand_mem,
      &eval_audit_ts,
      None,
      gens_mem,
      transcript,
    );

    (
      (eval_ops_addr, eval_read_ts, eval_audit_ts),
      (proof_ops_addr, proof_read_ts, proof_audit_ts),
    )
  }

  fn prove(
    rand: (&Vec<Scalar>, &Vec<Scalar>),
    dense: &SparseMatPolynomialAsDense,
    derefs: &Derefs,
    gens: &SparseMatPolyCommitmentGens,
    transcript: &mut Transcript,
  ) -> Self {
    transcript.append_protocol_name(HashLayerProof::protocol_name());

    let (rand_mem, rand_ops) = rand;

    // decommit derefs at rand_ops
    let eval_row_ops_val = derefs.row_ops_val.evaluate(&rand_ops);
    let eval_col_ops_val = derefs.col_ops_val.evaluate(&rand_ops);
    let proof_derefs = DerefsEvalProof::prove(
      derefs,
      &eval_row_ops_val,
      &eval_col_ops_val,
      &rand_ops,
      &gens.gens_derefs,
      transcript,
    );
    let eval_derefs = (eval_row_ops_val, eval_col_ops_val);

    // decommit val at rand_ops
    let eval_val = dense.val.evaluate(&rand_ops);
    let (proof_val, _comm_val_eval) = PolyEvalProof::prove(
      &dense.val,
      None,
      &rand_ops,
      &eval_val,
      None,
      &gens.gens_ops,
      transcript,
    );

    // decommit read-ts, ops-addr at rand_ops and audit-ts at rand_mem
    let (eval_row, proof_row) = HashLayerProof::prove_helper(
      (&rand_mem, &rand_ops),
      &dense.row,
      &gens.gens_mem,
      &gens.gens_ops,
      transcript,
    );

    // decommit read-ts, ops-addr at rand_ops and audit-ts at rand_mem
    let (eval_col, proof_col) = HashLayerProof::prove_helper(
      (&rand_mem, &rand_ops),
      &dense.col,
      &gens.gens_mem,
      &gens.gens_ops,
      transcript,
    );

    HashLayerProof {
      eval_row,
      proof_row,
      eval_col,
      proof_col,
      eval_derefs,
      proof_derefs,
      eval_val,
      proof_val,
    }
  }

  fn verify_helper(
    rand: &(&Vec<Scalar>, &Vec<Scalar>),
    proofs: &(PolyEvalProof, PolyEvalProof, PolyEvalProof),
    claims: &(Scalar, Scalar, Scalar, Scalar),
    comm: &AddrTimestampsCommitment,
    gens_ops: &PolyCommitmentGens,
    gens_mem: &PolyCommitmentGens,
    eval_ops_val: &Scalar,
    eval_ops_addr: &Scalar,
    eval_read_ts: &Scalar,
    eval_audit_ts: &Scalar,
    r: &Vec<Scalar>,
    r_hash: &Scalar,
    r_multiset_check: &Scalar,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let r_hash_sqr = r_hash * r_hash;
    let hash_func = |addr: &Scalar, val: &Scalar, ts: &Scalar| -> Scalar {
      ts * &r_hash_sqr + val * r_hash + addr
    };

    let (rand_mem, rand_ops) = rand;
    let (claim_init, claim_read, claim_write, claim_audit) = claims;
    let (proof_ops_addr, proof_read_ts, proof_audit_ts) = proofs;

    // init
    let eval_init_addr = IdentityPolynomial::new(rand_mem.len()).evaluate(rand_mem);
    let eval_init_val = EqPolynomial::new(r.clone()).evaluate(rand_mem);
    let hash_init_at_rand_mem =
      hash_func(&eval_init_addr, &eval_init_val, &Scalar::zero()) - r_multiset_check; // verify the claim_last of init chunk
    assert_eq!(&hash_init_at_rand_mem, claim_init);

    // read
    eval_ops_addr.append_to_transcript(b"claim_eval_ops_addr", transcript);
    assert!(proof_ops_addr
      .verify_plain(
        gens_ops,
        transcript,
        rand_ops,
        &eval_ops_addr,
        &comm.ops_addr,
      )
      .is_ok());

    eval_read_ts.append_to_transcript(b"claim_eval_read_ts", transcript);
    assert!(proof_read_ts
      .verify_plain(gens_ops, transcript, rand_ops, &eval_read_ts, &comm.read_ts)
      .is_ok());
    let hash_read_at_rand_ops =
      hash_func(&eval_ops_addr, eval_ops_val, &eval_read_ts) - r_multiset_check; // verify the claim_last of init chunk
    assert_eq!(&hash_read_at_rand_ops, claim_read);

    // write: shares addr, val component; only decommit write_ts
    let eval_write_ts = eval_read_ts + &Scalar::one();
    let hash_write_at_rand_ops =
      hash_func(&eval_ops_addr, &eval_ops_val, &eval_write_ts) - r_multiset_check; // verify the claim_last of init chunk
    assert_eq!(&hash_write_at_rand_ops, claim_write);

    // audit: shares addr and val with init
    let eval_audit_addr = eval_init_addr;
    let eval_audit_val = eval_init_val;
    eval_audit_ts.append_to_transcript(b"claim_eval_audit_ts", transcript);
    assert!(proof_audit_ts
      .verify_plain(
        gens_mem,
        transcript,
        rand_mem,
        eval_audit_ts,
        &comm.audit_ts,
      )
      .is_ok());

    let hash_audit_at_rand_mem =
      hash_func(&eval_audit_addr, &eval_audit_val, &eval_audit_ts) - r_multiset_check;
    assert_eq!(&hash_audit_at_rand_mem, claim_audit); // verify the last step of the sum-check for audit

    Ok(())
  }

  fn verify(
    &self,
    rand: (&Vec<Scalar>, &Vec<Scalar>),
    claims_row: &(Scalar, Scalar, Scalar, Scalar),
    claims_col: &(Scalar, Scalar, Scalar, Scalar),
    claims_val: &(Scalar, Scalar, Scalar),
    comm: &SparseMatPolyCommitment,
    gens: &SparseMatPolyCommitmentGens,
    comm_derefs: &DerefsCommitment,
    rx: &Vec<Scalar>,
    ry: &Vec<Scalar>,
    r_hash: &Scalar,
    r_multiset_check: &Scalar,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(HashLayerProof::protocol_name());

    let (rand_mem, rand_ops) = rand;

    // verify derefs at rand_ops
    let (eval_row_ops_val, eval_col_ops_val) = self.eval_derefs;
    assert!(self
      .proof_derefs
      .verify(
        &rand_ops,
        &eval_row_ops_val,
        &eval_col_ops_val,
        &gens.gens_derefs,
        comm_derefs,
        transcript
      )
      .is_ok());

    // verify the decommitments used in evaluation sum-check
    let (claim_row_ops_val, claim_col_ops_val, claim_val) = claims_val;
    assert_eq!(*claim_row_ops_val, eval_row_ops_val);
    assert_eq!(*claim_col_ops_val, eval_col_ops_val);
    assert_eq!(*claim_val, self.eval_val);
    assert!(self
      .proof_val
      .verify_plain(
        &gens.gens_ops,
        transcript,
        &rand_ops,
        claim_val,
        &comm.comm_val,
      )
      .is_ok());

    let (eval_ops_addr, eval_read_ts, eval_audit_ts) = self.eval_row;
    assert!(HashLayerProof::verify_helper(
      &(rand_mem, rand_ops),
      &self.proof_row,
      &claims_row,
      &comm.comm_row,
      &gens.gens_ops,
      &gens.gens_mem,
      &eval_row_ops_val,
      &eval_ops_addr,
      &eval_read_ts,
      &eval_audit_ts,
      rx,
      r_hash,
      r_multiset_check,
      transcript,
    )
    .is_ok());

    let (eval_ops_addr, eval_read_ts, eval_audit_ts) = self.eval_col;
    assert!(HashLayerProof::verify_helper(
      &(rand_mem, rand_ops),
      &self.proof_col,
      &claims_col,
      &comm.comm_col,
      &gens.gens_ops,
      &gens.gens_mem,
      &eval_col_ops_val,
      &eval_ops_addr,
      &eval_read_ts,
      &eval_audit_ts,
      ry,
      r_hash,
      r_multiset_check,
      transcript,
    )
    .is_ok());

    Ok(())
  }
}

#[derive(Debug, Serialize, Deserialize)]
struct ProductLayerProof {
  eval_row: (Scalar, Scalar, Scalar, Scalar),
  eval_col: (Scalar, Scalar, Scalar, Scalar),
  eval_val: (Scalar, Scalar),
  proof_mem: ProductCircuitEvalProofBatched,
  proof_ops: ProductCircuitEvalProofBatched,
}

impl ProductLayerProof {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial product layer proof"
  }

  pub fn prove(
    row_prod_layer: &mut MemCircuitProductLayer,
    col_prod_layer: &mut MemCircuitProductLayer,
    dense: &SparseMatPolynomialAsDense,
    derefs: &Derefs,
    eval: &Scalar,
    transcript: &mut Transcript,
  ) -> (Self, Vec<Scalar>, Vec<Scalar>) {
    transcript.append_protocol_name(ProductLayerProof::protocol_name());

    let (row_eval_init, row_eval_read, row_eval_write, row_eval_audit) = (
      row_prod_layer.init.evaluate(),
      row_prod_layer.read.evaluate(),
      row_prod_layer.write.evaluate(),
      row_prod_layer.audit.evaluate(),
    );

    // subset check
    assert_eq!(
      row_eval_init * row_eval_write,
      row_eval_read * row_eval_audit
    );

    row_eval_init.append_to_transcript(b"claim_row_eval_init", transcript);
    row_eval_read.append_to_transcript(b"claim_row_eval_read", transcript);
    row_eval_write.append_to_transcript(b"claim_row_eval_write", transcript);
    row_eval_audit.append_to_transcript(b"claim_row_eval_audit", transcript);

    let (col_eval_init, col_eval_read, col_eval_write, col_eval_audit) = (
      col_prod_layer.init.evaluate(),
      col_prod_layer.read.evaluate(),
      col_prod_layer.write.evaluate(),
      col_prod_layer.audit.evaluate(),
    );

    // subset check
    assert_eq!(
      col_eval_init * col_eval_write,
      col_eval_read * col_eval_audit
    );

    col_eval_init.append_to_transcript(b"claim_col_eval_init", transcript);
    col_eval_read.append_to_transcript(b"claim_col_eval_read", transcript);
    col_eval_write.append_to_transcript(b"claim_col_eval_write", transcript);
    col_eval_audit.append_to_transcript(b"claim_col_eval_audit", transcript);

    // evaluate sparse polynomial evaluation using two dotp checks
    let left = derefs.row_ops_val.clone();
    let right = derefs.col_ops_val.clone();
    let weights = dense.val.clone();

    // build two dot product circuits to prove evaluation of sparse polynomial
    let mut dotp_circuit = DotProductCircuit::new(left, right, weights);
    let (mut dotp_circuit_left, mut dotp_circuit_right) = dotp_circuit.split();

    let (eval_dotp_left, eval_dotp_right) =
      (dotp_circuit_left.evaluate(), dotp_circuit_right.evaluate());

    eval_dotp_left.append_to_transcript(b"claim_eval_dotp_left", transcript);
    eval_dotp_right.append_to_transcript(b"claim_eval_dotp_right", transcript);
    assert_eq!(&eval_dotp_left + eval_dotp_right, *eval);
    let (proof_mem, rand_mem) = ProductCircuitEvalProofBatched::prove(
      &mut vec![
        &mut row_prod_layer.init,
        &mut row_prod_layer.audit,
        &mut col_prod_layer.init,
        &mut col_prod_layer.audit,
      ],
      &mut Vec::new(),
      transcript,
    );

    // The number of operations into the memory encoded by rx and ry are always the same (by design)
    // So we can produce a batched product proof for all of them at the same time.
    // prove the correctness of claim_row_eval_read, claim_row_eval_write, claim_col_eval_read, and claim_col_eval_write
    let (proof_ops, rand_ops) = ProductCircuitEvalProofBatched::prove(
      &mut vec![
        &mut row_prod_layer.read,
        &mut row_prod_layer.write,
        &mut col_prod_layer.read,
        &mut col_prod_layer.write,
      ],
      &mut vec![&mut dotp_circuit_left, &mut dotp_circuit_right],
      transcript,
    );

    let product_layer_proof = ProductLayerProof {
      eval_row: (row_eval_init, row_eval_read, row_eval_write, row_eval_audit),
      eval_col: (col_eval_init, col_eval_read, col_eval_write, col_eval_audit),
      eval_val: (eval_dotp_left, eval_dotp_right),
      proof_mem,
      proof_ops,
    };

    let product_layer_proof_encoded: Vec<u8> = bincode::serialize(&product_layer_proof).unwrap();
    println!(
      "Length of product_layer_proof is: {:?}",
      product_layer_proof_encoded.len()
    );

    (product_layer_proof, rand_mem, rand_ops)
  }

  pub fn verify(
    &self,
    num_ops: usize,
    num_cells: usize,
    eval: &Scalar,
    transcript: &mut Transcript,
  ) -> Result<(Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>), ProofVerifyError> {
    transcript.append_protocol_name(ProductLayerProof::protocol_name());

    let start = Instant::now();
    // subset check
    let (row_eval_init, row_eval_read, row_eval_write, row_eval_audit) = self.eval_row;
    assert_eq!(
      row_eval_init * row_eval_write,
      row_eval_read * row_eval_audit
    );

    row_eval_init.append_to_transcript(b"claim_row_eval_init", transcript);
    row_eval_read.append_to_transcript(b"claim_row_eval_read", transcript);
    row_eval_write.append_to_transcript(b"claim_row_eval_write", transcript);
    row_eval_audit.append_to_transcript(b"claim_row_eval_audit", transcript);

    // subset check
    let (col_eval_init, col_eval_read, col_eval_write, col_eval_audit) = self.eval_col;
    assert_eq!(
      col_eval_init * col_eval_write,
      col_eval_read * col_eval_audit
    );

    col_eval_init.append_to_transcript(b"claim_col_eval_init", transcript);
    col_eval_read.append_to_transcript(b"claim_col_eval_read", transcript);
    col_eval_write.append_to_transcript(b"claim_col_eval_write", transcript);
    col_eval_audit.append_to_transcript(b"claim_col_eval_audit", transcript);

    // verify the evaluation of the sparse polynomial
    let (eval_dotp_left, eval_dotp_right) = self.eval_val;
    assert_eq!(&eval_dotp_left + &eval_dotp_right, *eval);
    eval_dotp_left.append_to_transcript(b"claim_eval_dotp_left", transcript);
    eval_dotp_right.append_to_transcript(b"claim_eval_dotp_right", transcript);

    // verify the correctness of claim_row_eval_init and claim_row_eval_audit
    let (claims_mem, rand_mem) = self.proof_mem.verify(
      &vec![row_eval_init, row_eval_audit, col_eval_init, col_eval_audit],
      &Vec::new(),
      num_cells,
      transcript,
    );

    // verify the correctness of claim_row_eval_read, claim_row_eval_write, claim_col_eval_read, and claim_col_eval_write
    let (claims_ops, rand_ops) = self.proof_ops.verify(
      &vec![row_eval_read, row_eval_write, col_eval_read, col_eval_write],
      &vec![eval_dotp_left, eval_dotp_right],
      num_ops,
      transcript,
    );
    let duration = start.elapsed();
    println!("Verifying product proof took {:?}", duration);

    Ok((claims_mem, rand_mem, claims_ops, rand_ops))
  }
}

#[derive(Debug, Serialize, Deserialize)]
struct PolyEvalNetworkProof {
  proof_prod_layer: ProductLayerProof,
  proof_hash_layer: HashLayerProof,
}

impl PolyEvalNetworkProof {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial memory circuit proof"
  }

  pub fn prove(
    mem_circuit: &mut MemCircuit,
    dense: &SparseMatPolynomialAsDense,
    derefs: &Derefs,
    eval: &Scalar,
    gens: &SparseMatPolyCommitmentGens,
    transcript: &mut Transcript,
  ) -> Self {
    transcript.append_protocol_name(PolyEvalNetworkProof::protocol_name());

    let (proof_prod_layer, rand_mem, rand_ops) = ProductLayerProof::prove(
      &mut mem_circuit.row_layers.prod_layer,
      &mut mem_circuit.col_layers.prod_layer,
      dense,
      derefs,
      eval,
      transcript,
    );

    // proof of hash layer for row and col
    let proof_hash_layer =
      HashLayerProof::prove((&rand_mem, &rand_ops), dense, derefs, gens, transcript);

    let poly_eval_network_proof = PolyEvalNetworkProof {
      proof_prod_layer,
      proof_hash_layer,
    };

    let poly_eval_network_proof_encoded: Vec<u8> = bincode::serialize(&poly_eval_network_proof).unwrap();
    println!(
      "Length of poly_eval_network_proof is: {:?}",
      poly_eval_network_proof_encoded.len()
    );

    poly_eval_network_proof
  }

  pub fn verify(
    &self,
    comm: &SparseMatPolyCommitment,
    comm_derefs: &DerefsCommitment,
    eval: &Scalar,
    gens: &SparseMatPolyCommitmentGens,
    rx: &Vec<Scalar>,
    ry: &Vec<Scalar>,
    r_hash: &Scalar,
    r_multiset_check: &Scalar,
    nz: usize,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(PolyEvalNetworkProof::protocol_name());

    let num_ops = nz.next_power_of_two();

    let rx_len = rx.len();
    let ry_len = ry.len();

    let num_cells = rx_len.pow2();
    assert_eq!(rx_len, ry_len);

    let (claims_mem, rand_mem, claims_ops, rand_ops) = self
      .proof_prod_layer
      .verify(num_ops, num_cells, eval, transcript)
      .unwrap();

    assert_eq!(claims_mem.len(), 4);
    assert_eq!(claims_ops.len(), 7);

    let start = Instant::now();
    // verify the proof of hash layer for row
    assert!(self
      .proof_hash_layer
      .verify(
        (&rand_mem, &rand_ops),
        &(claims_mem[0], claims_ops[0], claims_ops[1], claims_mem[1],),
        &(claims_mem[2], claims_ops[2], claims_ops[3], claims_mem[3],),
        &(claims_ops[4], claims_ops[5], claims_ops[6]),
        comm,
        gens,
        comm_derefs,
        rx,
        ry,
        r_hash,
        r_multiset_check,
        transcript
      )
      .is_ok());
    let duration = start.elapsed();
    println!("Verifying hash layer proof took {:?}", duration);

    Ok(())
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SparseMatPolyEvalProof {
  comm_derefs: DerefsCommitment,
  poly_eval_network_proof: PolyEvalNetworkProof,
}

#[allow(dead_code)]
impl SparseMatPolyEvalProof {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial evaluation proof"
  }

  fn equalize(rx: &Vec<Scalar>, ry: &Vec<Scalar>) -> (Vec<Scalar>, Vec<Scalar>) {
    if rx.len() < ry.len() {
      let diff = ry.len() - rx.len();
      let mut rx_ext = vec![Scalar::zero(); diff];
      rx_ext.extend(rx);
      (rx_ext, ry.clone())
    } else if rx.len() > ry.len() {
      let diff = rx.len() - ry.len();
      let mut ry_ext = vec![Scalar::zero(); diff];
      ry_ext.extend(ry);
      (rx.clone(), ry_ext)
    } else {
      (rx.clone(), ry.clone())
    }
  }

  pub fn prove(
    dense: &SparseMatPolynomialAsDense,
    rx: &Vec<Scalar>, // point at which the polynomial is evaluated
    ry: &Vec<Scalar>,
    _eval_table_rx: &Vec<Scalar>,
    _eval_table_ry: &Vec<Scalar>,
    eval: Scalar, // evaluation of \widetilde{M}(r = (rx,ry))
    gens: &SparseMatPolyCommitmentGens,
    transcript: &mut Transcript,
  ) -> SparseMatPolyEvalProof {
    transcript.append_protocol_name(SparseMatPolyEvalProof::protocol_name());

    // equalize the lengths of rx and ry
    let (rx_ext, ry_ext) = SparseMatPolyEvalProof::equalize(rx, ry);

    let eval_table_rx = EqPolynomial::new(rx_ext.clone()).evals();
    let eval_table_ry = EqPolynomial::new(ry_ext.clone()).evals();

    let start = Instant::now();
    let derefs = dense.deref(&eval_table_rx, &eval_table_ry);
    let duration = start.elapsed();
    println!("Time to deref memory addresses {:?}", duration);

    // commit to non-deterministic choices of the prover i.e., eval_cicruit.poly_row_deref and eval_cicruit.poly_col_deref
    let start = Instant::now();
    let comm_derefs = derefs.commit(&gens.gens_derefs);
    comm_derefs.append_to_transcript(b"comm_poly_row_col_ops_val", transcript);
    let duration = start.elapsed();
    println!("Time to commit to non-det derefs {:?}", duration);

    // produce a random element from the transcript for hash function
    let r_hash = transcript.challenge_scalar(b"challenge_r_hash");
    let r_multiset_check = transcript.challenge_scalar(b"challenge_r_multiset_check");

    let start = Instant::now();
    // build a network to evaluate the sparse polynomial
    let mut net = PolyEvalNetwork::new(
      dense,
      &derefs,
      &rx_ext,
      &ry_ext,
      &eval_table_rx,
      &eval_table_ry,
      &r_hash,
      &r_multiset_check,
    );
    //debug_assert!(net.evaluate() == eval);

    let duration = start.elapsed();
    println!("Time to build the layered network is: {:?}", duration);

    let start = Instant::now();
    let poly_eval_network_proof = PolyEvalNetworkProof::prove(
      &mut net.mem_circuit,
      &dense,
      &derefs,
      &eval,
      gens,
      transcript,
    );
    let duration = start.elapsed();
    println!("Time to produce poly_eval_network_proof {:?}", duration);

    SparseMatPolyEvalProof {
      comm_derefs,
      poly_eval_network_proof,
    }
  }

  pub fn verify(
    &self,
    comm: &SparseMatPolyCommitment,
    rx: &Vec<Scalar>, // point at which the polynomial is evaluated
    ry: &Vec<Scalar>,
    eval: Scalar, // evaluation of \widetilde{M}(r = (rx,ry))
    nz: usize,
    gens: &SparseMatPolyCommitmentGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let start = Instant::now();
    transcript.append_protocol_name(SparseMatPolyEvalProof::protocol_name());

    // equalize the lengths of rx and ry
    let (rx_ext, ry_ext) = SparseMatPolyEvalProof::equalize(rx, ry);

    // add claims to transcript and obtain challenges for randomized mem-check circuit
    self
      .comm_derefs
      .append_to_transcript(b"comm_poly_row_col_ops_val", transcript);

    // produce a random element from the transcript for hash function
    let r_hash = transcript.challenge_scalar(b"challenge_r_hash");
    let r_multiset_check = transcript.challenge_scalar(b"challenge_r_multiset_check");

    assert!(self
      .poly_eval_network_proof
      .verify(
        comm,
        &self.comm_derefs,
        &eval,
        gens,
        &rx_ext,
        &ry_ext,
        &r_hash,
        &r_multiset_check,
        nz,
        transcript,
      )
      .is_ok());

    let duration = start.elapsed();
    println!("Verifying sparse eval proof took {:?}", duration);

    Ok(())
  }
}

pub struct SparsePolyEntry {
  idx: usize,
  val: Scalar,
}

impl SparsePolyEntry {
  pub fn new(idx: usize, val: Scalar) -> Self {
    SparsePolyEntry { idx, val }
  }
}

pub struct SparsePolynomial {
  num_vars: usize,
  Z: Vec<SparsePolyEntry>,
}

impl SparsePolynomial {
  pub fn new(num_vars: usize, Z: Vec<SparsePolyEntry>) -> Self {
    SparsePolynomial { num_vars, Z }
  }

  fn compute_chi(a: &Vec<bool>, r: &Vec<Scalar>) -> Scalar {
    assert_eq!(a.len(), r.len());
    let mut chi_i = Scalar::one();
    for j in 0..r.len() {
      if a[j] {
        chi_i *= r[j];
      } else {
        chi_i *= Scalar::one() - r[j];
      }
    }
    chi_i
  }

  // Takes O(n log n). TODO: do this in O(n) where n is the number of entries in Z
  pub fn evaluate(&self, r: &Vec<Scalar>) -> Scalar {
    assert_eq!(self.num_vars, r.len());

    (0..self.Z.len())
      .map(|i| {
        let bits = self.Z[i].idx.get_bits(r.len());
        SparsePolynomial::compute_chi(&bits, r) * self.Z[i].val
      })
      .sum()
  }
}

mod tests {
  #[cfg(test)]
  use super::*;
  #[cfg(test)]
  use rand::rngs::OsRng;
  #[cfg(test)]
  use rand::RngCore;
  #[test]
  fn check_sparse_polyeval_proof() {
    let mut csprng: OsRng = OsRng;

    let num_nz_entries = 256;
    let num_rows = 256;
    let num_cols = 256;
    let num_vars_x = num_rows.log2();
    let num_vars_y = num_cols.log2();

    let mut M: Vec<SparseMatEntry> = Vec::new();

    for _i in 0..num_nz_entries {
      M.push(SparseMatEntry::new(
        (csprng.next_u64() % (num_rows as u64)) as usize,
        (csprng.next_u64() % (num_cols as u64)) as usize,
        Scalar::random(&mut csprng),
      ));
    }

    let poly_M = SparseMatPolynomial::new(num_vars_x, num_vars_y, M);
    let poly_M_size = poly_M.size();
    let gens = SparseMatPolyCommitmentGens::new(&poly_M_size, b"gens_sparse_poly");

    // commitment
    let (poly_comm, dense) = poly_M.commit(&gens);

    // evaluation
    let rx: Vec<Scalar> = (0..num_vars_x)
      .map(|_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    let ry: Vec<Scalar> = (0..num_vars_y)
      .map(|_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    let eval = poly_M.evaluate(&rx, &ry);

    let eval_table_rx = EqPolynomial::new(rx.clone()).evals();
    let eval_table_ry = EqPolynomial::new(ry.clone()).evals();

    let mut prover_transcript = Transcript::new(b"example");

    let proof = SparseMatPolyEvalProof::prove(
      &dense,
      &rx,
      &ry,
      &eval_table_rx,
      &eval_table_ry,
      eval,
      &gens,
      &mut prover_transcript,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(
        &poly_comm,
        &rx,
        &ry,
        eval,
        num_nz_entries,
        &gens,
        &mut verifier_transcript,
      )
      .is_ok());
  }
}
