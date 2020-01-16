#[allow(dead_code)]
use super::dense_mlpoly::DensePolynomial;
use super::dense_mlpoly::{
  ConstPolynomial, DensePolynomialSize, EqPolynomial, IdentityPolynomial, PolyCommitment,
  PolyCommitmentGens, PolyEvalProof,
};
use super::errors::ProofVerifyError;
use super::math::Math;
use super::scalar::Scalar;
use super::sumcheck::SumcheckInstanceProof;
use super::transcript::{AppendToTranscript, ProofTranscript};
use super::unipoly::CubicPoly;
use super::unipoly::SumcheckProofPolyABI;
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
  write_ts: DensePolynomial,
  audit_ts: DensePolynomial,
}

pub struct Values {
  row_ops_val: DensePolynomial,
  col_ops_val: DensePolynomial,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ValuesCommitment {
  comm_row_ops_val: PolyCommitment,
  comm_col_ops_val: PolyCommitment,
}

impl Values {
  pub fn commit(
    &self,
    gens_row: &AddrTimestampsGens,
    gens_col: &AddrTimestampsGens,
  ) -> ValuesCommitment {
    let blinds = None;
    let comm_row_ops_val = self.row_ops_val.commit(blinds, &gens_row.gens_ops);
    let comm_col_ops_val = self.col_ops_val.commit(blinds, &gens_col.gens_ops);
    ValuesCommitment {
      comm_row_ops_val,
      comm_col_ops_val,
    }
  }
}

impl AppendToTranscript for ValuesCommitment {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(b"values_commitment", b"begin_values_commitment");
    self
      .comm_row_ops_val
      .append_to_transcript(label, transcript);
    self
      .comm_col_ops_val
      .append_to_transcript(label, transcript);
    transcript.append_message(b"values_commitment", b"end_values_commitment");
  }
}

struct AddrTimestampsSize {
  mem_size: DensePolynomialSize,
  ops_size: DensePolynomialSize,
}

pub struct SparseMatPolynomialAsDense {
  val: Vec<Scalar>,
  row: AddrTimestamps,
  col: AddrTimestamps,
}

pub struct SparseMatPolynomialSize {
  val_size: DensePolynomialSize,
  row_size: AddrTimestampsSize,
  col_size: AddrTimestampsSize,
}

pub struct AddrTimestampsGens {
  gens_mem: PolyCommitmentGens,
  gens_ops: PolyCommitmentGens,
}

pub struct SparseMatPolyCommitmentGens {
  gens_val: PolyCommitmentGens,
  gens_row: AddrTimestampsGens,
  gens_col: AddrTimestampsGens,
}

impl SparseMatPolyCommitmentGens {
  pub fn new(size: &SparseMatPolynomialSize, label: &'static [u8]) -> SparseMatPolyCommitmentGens {
    let gens_val = PolyCommitmentGens::new(&size.val_size, label);
    let gens_row = AddrTimestampsGens {
      gens_mem: PolyCommitmentGens::new(&size.row_size.mem_size, label),
      gens_ops: PolyCommitmentGens::new(&size.row_size.ops_size, label),
    };
    let gens_col = AddrTimestampsGens {
      gens_mem: PolyCommitmentGens::new(&size.col_size.mem_size, label),
      gens_ops: PolyCommitmentGens::new(&size.col_size.ops_size, label),
    };
    SparseMatPolyCommitmentGens {
      gens_val,
      gens_row,
      gens_col,
    }
  }
}

#[derive(Debug, Serialize, Deserialize)]
struct AddrTimestampsCommitment {
  ops_addr: PolyCommitment,
  read_ts: PolyCommitment,
  write_ts: PolyCommitment,
  audit_ts: PolyCommitment,
}

impl AddrTimestamps {
  pub fn new(num_cells: usize, ops_addr: Vec<usize>) -> Self {
    let num_ops = ops_addr.len();

    let mut read_ts = vec![0usize; num_ops];
    let mut write_ts = vec![0usize; num_ops];
    let mut audit_ts = vec![0usize; num_cells];

    // since read timestamps are trustworthy, we can simply increment the r-ts to obtain a w-ts
    // this is sufficient to ensure that the write-set, consisting of (addr, val, ts) tuples, is a set
    for i in 0..num_ops {
      let addr = ops_addr[i];
      assert!(addr < num_cells);
      let r_ts = audit_ts[addr];
      read_ts[i] = r_ts;

      let w_ts = r_ts + 1;
      write_ts[i] = w_ts;
      audit_ts[addr] = w_ts;
    }

    AddrTimestamps {
      ops_addr: DensePolynomial::from_usize(&ops_addr),
      ops_addr_usize: ops_addr,
      read_ts: DensePolynomial::from_usize(&read_ts),
      write_ts: DensePolynomial::from_usize(&write_ts),
      audit_ts: DensePolynomial::from_usize(&audit_ts),
    }
  }

  pub fn size(&self) -> AddrTimestampsSize {
    AddrTimestampsSize {
      mem_size: self.audit_ts.size(),
      ops_size: self.read_ts.size(),
    }
  }

  pub fn commit(&self, gens: &AddrTimestampsGens) -> AddrTimestampsCommitment {
    let blinds = None;

    AddrTimestampsCommitment {
      ops_addr: self.ops_addr.commit(blinds, &gens.gens_ops),
      read_ts: self.read_ts.commit(blinds, &gens.gens_ops),
      write_ts: self.write_ts.commit(blinds, &gens.gens_ops),
      audit_ts: self.audit_ts.commit(blinds, &gens.gens_mem),
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

    let row = AddrTimestamps::new(self.num_vars_x.pow2(), ops_row);
    let col = AddrTimestamps::new(self.num_vars_y.pow2(), ops_col);

    SparseMatPolynomialAsDense { row, col, val }
  }

  pub fn size(&self) -> SparseMatPolynomialSize {
    let dense = self.sparse_to_dense_rep();
    SparseMatPolynomialSize {
      row_size: dense.row.size(),
      col_size: dense.col.size(),
      val_size: DensePolynomial::new(dense.val).size(),
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
    let comm_row = dense.row.commit(&gens.gens_row);
    let comm_col = dense.col.commit(&gens.gens_col);
    let comm_val = DensePolynomial::new(dense.val.clone()).commit(None, &gens.gens_val);
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
  pub fn deref(&self, row_mem_val: &Vec<Scalar>, col_mem_val: &Vec<Scalar>) -> Values {
    let row_ops_val = self.row.deref(row_mem_val);
    let col_ops_val = self.col.deref(col_mem_val);

    Values {
      row_ops_val,
      col_ops_val,
    }
  }
}

// TODO: move this to sumcheck.rs
#[derive(Debug)]
struct ProductCircuit {
  left_vec: Vec<DensePolynomial>,
  right_vec: Vec<DensePolynomial>,
}

impl ProductCircuit {
  fn compute_layer(
    inp_left: &DensePolynomial,
    inp_right: &DensePolynomial,
  ) -> (DensePolynomial, DensePolynomial) {
    let len = inp_left.len() + inp_right.len();
    let outp_left = (0..len / 4)
      .map(|i| &inp_left[i] * &inp_right[i])
      .collect::<Vec<Scalar>>();
    let outp_right = (len / 4..len / 2)
      .map(|i| &inp_left[i] * &inp_right[i])
      .collect::<Vec<Scalar>>();

    (
      DensePolynomial::new(outp_left),
      DensePolynomial::new(outp_right),
    )
  }

  pub fn new(poly: &DensePolynomial) -> Self {
    let mut left_vec: Vec<DensePolynomial> = Vec::new();
    let mut right_vec: Vec<DensePolynomial> = Vec::new();

    let num_layers = poly.len().log2();
    let (outp_left, outp_right) = poly.split(poly.len() / 2);

    left_vec.push(outp_left);
    right_vec.push(outp_right);

    for i in 0..num_layers - 1 {
      let (outp_left, outp_right) = ProductCircuit::compute_layer(&left_vec[i], &right_vec[i]);
      left_vec.push(outp_left);
      right_vec.push(outp_right);
    }

    ProductCircuit {
      left_vec,
      right_vec,
    }
  }

  pub fn evaluate(&self) -> Scalar {
    let len = self.left_vec.len();
    assert_eq!(self.left_vec[len - 1].get_num_vars(), 0);
    assert_eq!(self.right_vec[len - 1].get_num_vars(), 0);
    self.left_vec[len - 1][0] * self.right_vec[len - 1][0]
  }
}

#[allow(dead_code)]
#[derive(Debug, Serialize, Deserialize)]
struct LayerProof<T: SumcheckProofPolyABI + AppendToTranscript> {
  proof: SumcheckInstanceProof<T>,
  claims: Vec<Scalar>,
}

#[allow(dead_code)]
impl<T: SumcheckProofPolyABI + AppendToTranscript> LayerProof<T> {
  fn verify(
    &self,
    claim: Scalar,
    num_rounds: usize,
    transcript: &mut Transcript,
  ) -> (Scalar, Vec<Scalar>) {
    self.proof.verify(claim, num_rounds, transcript).unwrap()
  }
}

#[derive(Debug, Serialize, Deserialize)]
struct ProductCircuitEvalProof {
  proof: Vec<LayerProof<CubicPoly>>,
}

impl ProductCircuitEvalProof {
  pub fn prove(
    circuit: &mut ProductCircuit,
    transcript: &mut Transcript,
  ) -> (Self, Scalar, Vec<Scalar>) {
    let mut proof: Vec<LayerProof<CubicPoly>> = Vec::new();
    let num_layers = circuit.left_vec.len();

    let mut claim = circuit.evaluate();
    let mut rand = Vec::new();
    for layer_id in (0..num_layers).rev() {
      let len = circuit.left_vec[layer_id].len() + circuit.right_vec[layer_id].len();

      let mut poly_C = DensePolynomial::new(EqPolynomial::new(rand.clone()).evals());
      assert_eq!(poly_C.len(), len / 2);

      let num_rounds_prod = poly_C.len().log2();
      let comb_func_prod = |poly_A_comp: &Scalar,
                            poly_B_comp: &Scalar,
                            poly_C_comp: &Scalar|
       -> Scalar { poly_A_comp * poly_B_comp * poly_C_comp };
      let (proof_prod, rand_prod, claims_prod) = SumcheckInstanceProof::<CubicPoly>::prove(
        &claim,
        num_rounds_prod,
        &mut circuit.left_vec[layer_id],
        &mut circuit.right_vec[layer_id],
        &mut poly_C,
        comb_func_prod,
        transcript,
      );

      transcript.append_scalar(b"claim_prod_left", &claims_prod[0]);
      transcript.append_scalar(b"claim_prod_right", &claims_prod[1]);

      // produce a random challenge
      let r_layer = transcript.challenge_scalar(b"challenge_r_layer");
      claim = &claims_prod[0] + &r_layer * (&claims_prod[1] - &claims_prod[0]);

      let mut ext = vec![r_layer];
      ext.extend(rand_prod);
      rand = ext;

      proof.push(LayerProof {
        proof: proof_prod,
        claims: claims_prod[0..claims_prod.len() - 1].to_vec(),
      });
    }

    (ProductCircuitEvalProof { proof }, claim, rand)
  }

  pub fn verify(
    &self,
    eval: Scalar,
    len: usize,
    transcript: &mut Transcript,
  ) -> (Scalar, Vec<Scalar>) {
    let num_layers = len.log2();
    let mut claim = eval;
    let mut rand: Vec<Scalar> = Vec::new();
    let mut num_rounds = 0;
    assert_eq!(self.proof.len(), num_layers);
    for i in 0..num_layers {
      let (claim_last, rand_prod) = self.proof[i].verify(claim, num_rounds, transcript);

      let claims_prod = &self.proof[i].claims;
      transcript.append_scalar(b"claim_prod_left", &claims_prod[0]);
      transcript.append_scalar(b"claim_prod_right", &claims_prod[1]);

      assert_eq!(rand.len(), rand_prod.len());
      let eq: Scalar = (0..rand.len())
        .map(|i| {
          rand[i] * rand_prod[i] + (Scalar::one() - rand[i]) * (Scalar::one() - rand_prod[i])
        })
        .product();
      assert_eq!(claims_prod[0] * claims_prod[1] * eq, claim_last);

      // produce a random challenge
      let r_layer = transcript.challenge_scalar(b"challenge_r_layer");
      claim = (Scalar::one() - r_layer) * claims_prod[0] + r_layer * claims_prod[1];
      num_rounds = num_rounds + 1;
      let mut ext = vec![r_layer];
      ext.extend(rand_prod);
      rand = ext;
    }

    (claim, rand)
  }
}

#[derive(Debug)]
struct EvalCircuit {
  poly_val: DensePolynomial,
  poly_row_val: DensePolynomial,
  poly_col_val: DensePolynomial,
}

impl EvalCircuit {
  pub fn new(
    poly_row_val: DensePolynomial,
    poly_col_val: DensePolynomial,
    poly_val: DensePolynomial,
  ) -> Self {
    EvalCircuit {
      poly_val,
      poly_row_val,
      poly_col_val,
    }
  }

  pub fn evaluate(&self) -> Scalar {
    (0..self.poly_val.len())
      .map(|i| &self.poly_val[i] * &self.poly_row_val[i] * &self.poly_col_val[i])
      .sum()
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
    write_ts: &DensePolynomial,
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
          // at write time, addr is given by addrs, value is given by derefs, and ts is given by write_ts
          &hash_func(&addrs[i], &derefs[i], &write_ts[i]) - r_multiset_check
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
        &addr_timestamps.write_ts,
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
    eval_circuit: &EvalCircuit,
    dense: &SparseMatPolynomialAsDense,
    r_hash: &Scalar,
    r_multiset_check: &Scalar,
  ) -> MemCircuit {
    let row_layers = MemCircuitLayers::new(
      eval_table_rx,
      &dense.row,
      &eval_circuit.poly_row_val,
      r_hash,
      r_multiset_check,
    );
    let col_layers = MemCircuitLayers::new(
      eval_table_ry,
      &dense.col,
      &eval_circuit.poly_col_val,
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
  eval_circuit: EvalCircuit,
  mem_circuit: MemCircuit,
}

impl PolyEvalNetwork {
  pub fn new(
    dense: &SparseMatPolynomialAsDense,
    values: &Values,
    rx: &Vec<Scalar>,
    ry: &Vec<Scalar>,
    eval_table_rx: &Vec<Scalar>,
    eval_table_ry: &Vec<Scalar>,
    r_hash: &Scalar,
    r_multiset_check: &Scalar,
  ) -> Self {
    assert_eq!(rx.len().pow2(), eval_table_rx.len());
    assert_eq!(ry.len().pow2(), eval_table_ry.len());

    // build evaluation circuit
    let eval_circuit = EvalCircuit::new(
      values.row_ops_val.clone(),
      values.col_ops_val.clone(),
      DensePolynomial::new(dense.val.clone()),
    );

    // build memory checking circuit
    let mem_circuit = MemCircuit::new(
      eval_table_rx,
      eval_table_ry,
      &eval_circuit,
      &dense,
      &r_hash,
      &r_multiset_check,
    );

    PolyEvalNetwork {
      r: (rx.to_vec(), ry.to_vec()),
      eval_circuit,
      mem_circuit,
    }
  }

  pub fn evaluate(&self) -> Scalar {
    self.eval_circuit.evaluate()
  }
}

#[derive(Debug, Serialize, Deserialize)]
struct EvalCircuitProof {
  proof_eval: LayerProof<CubicPoly>,
  proof_row_eval: PolyEvalProof,
  proof_col_eval: PolyEvalProof,
  proof_val_eval: PolyEvalProof,
}

impl EvalCircuitProof {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial evaluation circuit proof"
  }

  pub fn prove(
    eval_circuit: &mut EvalCircuit,
    values: &Values,
    comm_values: &ValuesCommitment,
    comm_val: &PolyCommitment,
    gens_val: &PolyCommitmentGens,
    gens_values: &PolyCommitmentGens,
    eval: &Scalar, // evaluation of \widetilde{M}(r = (rx,ry))
    transcript: &mut Transcript,
  ) -> Self {
    transcript.append_protocol_name(EvalCircuitProof::protocol_name());

    // evaluation sum-check
    let poly_val = eval_circuit.poly_val.clone(); // clone because we need to use it to decommit below
    let num_rounds_eval = eval_circuit.poly_val.len().log2();
    let comb_func_eval = |poly_A_comp: &Scalar,
                          poly_B_comp: &Scalar,
                          poly_C_comp: &Scalar|
     -> Scalar { poly_A_comp * poly_B_comp * poly_C_comp };
    let (sc_proof_eval, r_eval, claims_eval) = SumcheckInstanceProof::<CubicPoly>::prove(
      &eval,
      num_rounds_eval,
      &mut eval_circuit.poly_row_val,
      &mut eval_circuit.poly_col_val,
      &mut eval_circuit.poly_val,
      comb_func_eval,
      transcript,
    );
    transcript.append_scalar(b"claim_poly_row_val", &claims_eval[0]);
    transcript.append_scalar(b"claim_poly_col_val", &claims_eval[1]);
    transcript.append_scalar(b"claim_poly_val", &claims_eval[2]);

    // prove claim_poly_row_val and claim_poly_col_val
    let row_eval = claims_eval[0];
    debug_assert!(values.row_ops_val.evaluate(&r_eval) == row_eval);
    let blinds = None;
    let (proof_row_eval, _comm_row_eval) = PolyEvalProof::prove(
      &values.row_ops_val,
      &comm_values.comm_row_ops_val,
      blinds,
      &r_eval,
      &row_eval,
      &Scalar::zero(),
      gens_values,
      transcript,
    );

    let col_eval = claims_eval[1];
    debug_assert!(values.col_ops_val.evaluate(&r_eval) == col_eval);
    let blinds = None;
    let (proof_col_eval, _comm_col_eval) = PolyEvalProof::prove(
      &values.col_ops_val,
      &comm_values.comm_col_ops_val,
      blinds,
      &r_eval,
      &col_eval,
      &Scalar::zero(),
      gens_values,
      transcript,
    );

    // prove claim_vals using the dense polynomial commitment scheme
    let val_eval = claims_eval[2];
    debug_assert!(poly_val.evaluate(&r_eval) == claims_eval[2]);
    let (proof_val_eval, _comm_val_eval) = PolyEvalProof::prove(
      &poly_val,
      comm_val,
      blinds,
      &r_eval,
      &val_eval,
      &Scalar::zero(),
      gens_val,
      transcript,
    );

    let proof_eval = LayerProof {
      proof: sc_proof_eval,
      claims: claims_eval,
    };

    EvalCircuitProof {
      proof_eval,
      proof_row_eval,
      proof_col_eval,
      proof_val_eval,
    }
  }

  pub fn verify(
    &self,
    len: usize,
    comm_val: &PolyCommitment,
    gens_val: &PolyCommitmentGens,
    comm_values: &ValuesCommitment,
    gens_row: &PolyCommitmentGens,
    gens_col: &PolyCommitmentGens,
    eval: Scalar, // evaluation of \widetilde{M}(r = (rx,ry))
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let start = Instant::now();
    transcript.append_protocol_name(EvalCircuitProof::protocol_name());

    let num_rounds_eval = len.next_power_of_two().log2();
    let (claim_eval, r_eval) = self.proof_eval.verify(eval, num_rounds_eval, transcript);
    assert_eq!(
      claim_eval,
      self.proof_eval.claims[0] * self.proof_eval.claims[1] * self.proof_eval.claims[2]
    );

    transcript.append_scalar(b"claim_poly_row_val", &self.proof_eval.claims[0]);
    transcript.append_scalar(b"claim_poly_col_val", &self.proof_eval.claims[1]);
    transcript.append_scalar(b"claim_poly_val", &self.proof_eval.claims[2]);
    let duration = start.elapsed();
    println!("Verify: proof_eval took {:?}", duration);

    let start = Instant::now();
    assert!(self
      .proof_row_eval
      .verify_plain(
        gens_row,
        transcript,
        &r_eval,
        &self.proof_eval.claims[0],
        &comm_values.comm_row_ops_val,
      )
      .is_ok());

    assert!(self
      .proof_col_eval
      .verify_plain(
        gens_col,
        transcript,
        &r_eval,
        &self.proof_eval.claims[1],
        &comm_values.comm_col_ops_val,
      )
      .is_ok());

    assert!(self
      .proof_val_eval
      .verify_plain(
        gens_val,
        transcript,
        &r_eval,
        &self.proof_eval.claims[2],
        comm_val,
      )
      .is_ok());
    let duration = start.elapsed();
    println!("Verify: proof_row_col_val took {:?}", duration);

    Ok(())
  }
}

#[derive(Debug, Serialize, Deserialize)]
struct HashLayerProof {
  eval_audit_ts: Scalar,
  proof_audit_ts: PolyEvalProof,
  proof_read: PolyEvalProof,
  proof_write: PolyEvalProof,
}

impl HashLayerProof {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial hash layer proof"
  }

  fn prove(
    rand: (&Vec<Scalar>, &Vec<Scalar>, &Vec<Scalar>, &Vec<Scalar>),
    addr_timestamps: &AddrTimestamps,
    comm_addr_timestamps: &AddrTimestampsCommitment,
    hash_layer: &MemCircuitHashLayer,
    gens: &AddrTimestampsGens,
    transcript: &mut Transcript,
  ) -> Self {
    transcript.append_protocol_name(HashLayerProof::protocol_name());

    let (_rand_init, rand_read, rand_write, rand_audit) = rand;

    // read
    let eval_read = hash_layer.read.evaluate(rand_read);
    eval_read.append_to_transcript(b"claim_eval_read", transcript);
    let (proof_read, _comm_read_eval) = PolyEvalProof::prove(
      &hash_layer.read,
      &comm_addr_timestamps.ops_addr, // dummy parameter. TODO: remove it
      None,
      &rand_read,
      &eval_read,
      &Scalar::zero(), // TODO: make this optional parameter
      &gens.gens_ops,
      transcript,
    );

    // write
    let eval_write = hash_layer.write.evaluate(rand_write);
    eval_write.append_to_transcript(b"claim_eval_write", transcript);
    let (proof_write, _comm_write_eval) = PolyEvalProof::prove(
      &hash_layer.write,
      &comm_addr_timestamps.ops_addr,
      None,
      &rand_write,
      &eval_write,
      &Scalar::zero(), // TODO: make this optional parameter
      &gens.gens_ops,
      transcript,
    );

    // audit
    let eval_audit_ts = addr_timestamps.audit_ts.evaluate(rand_audit);
    eval_audit_ts.append_to_transcript(b"claim_eval_audit_ts", transcript);
    let (proof_audit_ts, _comm_audit_ts_eval) = PolyEvalProof::prove(
      &addr_timestamps.audit_ts,
      &comm_addr_timestamps.audit_ts,
      None,
      &rand_audit,
      &eval_audit_ts,
      &Scalar::zero(), // TODO: make this optional parameter
      &gens.gens_mem,
      transcript,
    );

    HashLayerProof {
      eval_audit_ts, // TODO: can be calculate on the verifier  side
      proof_audit_ts,
      proof_read,
      proof_write,
    }
  }

  fn verify(
    &self,
    rand: (&Vec<Scalar>, &Vec<Scalar>, &Vec<Scalar>, &Vec<Scalar>),
    claims: (&Scalar, &Scalar, &Scalar, &Scalar),
    comm: &AddrTimestampsCommitment,
    gens: &AddrTimestampsGens,
    comm_ops_val: &PolyCommitment,
    r: &Vec<Scalar>,
    r_hash: &Scalar,
    r_multiset_check: &Scalar,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(HashLayerProof::protocol_name());

    let r_hash_sqr = r_hash * r_hash;
    let hash_func = |addr: &Scalar, val: &Scalar, ts: &Scalar| -> Scalar {
      ts * &r_hash_sqr + val * r_hash + addr
    };

    let (rand_init, rand_read, rand_write, rand_audit) = rand;
    let (claim_init, claim_read, claim_write, claim_audit) = claims;

    // init
    let eval_init_addr = IdentityPolynomial::new(rand_init.len()).evaluate(rand_init);
    let eval_init_val = EqPolynomial::new(r.clone()).evaluate(rand_init);
    let hash_init_at_rand_init =
      hash_func(&eval_init_addr, &eval_init_val, &Scalar::zero()) - r_multiset_check; // verify the claim_last of init chunk
    assert_eq!(&hash_init_at_rand_init, claim_init);

    // read
    let eval_read = claim_read;
    eval_read.append_to_transcript(b"claim_eval_read", transcript);

    let comm_multiset_check =
      ConstPolynomial::new(rand_read.len(), -r_multiset_check).commit(&gens.gens_ops);

    assert!(self
      .proof_read
      .verify_plain_batched(
        &gens.gens_ops,
        transcript,
        rand_read,
        &eval_read,
        &[
          &comm.ops_addr,
          comm_ops_val,
          &comm.read_ts,
          &comm_multiset_check
        ],
        &[&Scalar::one(), r_hash, &r_hash_sqr, &Scalar::one()]
      )
      .is_ok());

    //write
    let eval_write = claim_write;
    eval_write.append_to_transcript(b"claim_eval_write", transcript);

    assert!(self
      .proof_write
      .verify_plain_batched(
        &gens.gens_ops,
        transcript,
        rand_write,
        &eval_write,
        &[
          &comm.ops_addr,
          comm_ops_val,
          &comm.write_ts,
          &comm_multiset_check
        ],
        &[&Scalar::one(), &r_hash, &r_hash_sqr, &Scalar::one()]
      )
      .is_ok());

    //audit
    let eval_audit_addr = IdentityPolynomial::new(rand_audit.len()).evaluate(rand_audit);
    let eval_audit_ts = self.eval_audit_ts;
    eval_audit_ts.append_to_transcript(b"claim_eval_audit_ts", transcript);
    assert!(self
      .proof_audit_ts
      .verify_plain(
        &gens.gens_mem,
        transcript,
        rand_audit,
        &eval_audit_ts,
        &comm.audit_ts,
      )
      .is_ok());

    let eval_audit_val = EqPolynomial::new(r.clone()).evaluate(rand_audit);
    let hash_audit_at_rand_audit =
      hash_func(&eval_audit_addr, &eval_audit_val, &eval_audit_ts) - r_multiset_check;
    assert_eq!(&hash_audit_at_rand_audit, claim_audit); // verify the last step of the sum-check for audit

    Ok(())
  }
}

#[derive(Debug, Serialize, Deserialize)]
struct MemCircuitLayersProof {
  eval_init: Scalar,
  eval_read: Scalar,
  eval_write: Scalar,
  eval_audit: Scalar,
  proof_prod_layer_init: ProductCircuitEvalProof,
  proof_prod_layer_read: ProductCircuitEvalProof,
  proof_prod_layer_write: ProductCircuitEvalProof,
  proof_prod_layer_audit: ProductCircuitEvalProof,
  proof_hash_layer: HashLayerProof,
}

impl MemCircuitLayersProof {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial memory circuit layers proof"
  }

  fn prove(
    mem_circuit_layers: &mut MemCircuitLayers,
    addr_timestamps: &AddrTimestamps,
    comm_addr_timestamps: &AddrTimestampsCommitment,
    gens: &AddrTimestampsGens,
    transcript: &mut Transcript,
  ) -> Self {
    transcript.append_protocol_name(MemCircuitLayersProof::protocol_name());

    let eval_init = mem_circuit_layers.prod_layer.init.evaluate();
    let eval_read = mem_circuit_layers.prod_layer.read.evaluate();
    let eval_write = mem_circuit_layers.prod_layer.write.evaluate();
    let eval_audit = mem_circuit_layers.prod_layer.audit.evaluate();

    assert_eq!(eval_init * eval_write, eval_read * eval_audit);

    eval_init.append_to_transcript(b"claim_eval_init", transcript);
    eval_read.append_to_transcript(b"claim_eval_read", transcript);
    eval_write.append_to_transcript(b"claim_eval_write", transcript);
    eval_audit.append_to_transcript(b"claim_eval_audit", transcript);

    let (proof_prod_layer_init, _claim_last_init, rand_init) =
      ProductCircuitEvalProof::prove(&mut mem_circuit_layers.prod_layer.init, transcript);

    let (proof_prod_layer_read, _claim_last_read, rand_read) =
      ProductCircuitEvalProof::prove(&mut mem_circuit_layers.prod_layer.read, transcript);

    let (proof_prod_layer_write, _claim_last_write, rand_write) =
      ProductCircuitEvalProof::prove(&mut mem_circuit_layers.prod_layer.write, transcript);

    let (proof_prod_layer_audit, _claim_last_audit, rand_audit) =
      ProductCircuitEvalProof::prove(&mut mem_circuit_layers.prod_layer.audit, transcript);

    let proof_hash_layer = HashLayerProof::prove(
      (&rand_init, &rand_read, &rand_write, &rand_audit),
      addr_timestamps,
      comm_addr_timestamps,
      &mem_circuit_layers.hash_layer,
      gens,
      transcript,
    );

    let proof_hash_layer_encoded: Vec<u8> = bincode::serialize(&proof_hash_layer).unwrap();
    println!(
      "Length of proof_hash_layer_encoded is: {:?}",
      proof_hash_layer_encoded.len()
    );

    let mem_circuit_layers_proof = MemCircuitLayersProof {
      eval_init,
      eval_read,
      eval_write,
      eval_audit,
      proof_prod_layer_init,
      proof_prod_layer_read,
      proof_prod_layer_write,
      proof_prod_layer_audit,
      proof_hash_layer,
    };

    let mem_circuit_layers_proof_encoded: Vec<u8> =
      bincode::serialize(&mem_circuit_layers_proof).unwrap();
    println!(
      "Length of mem_circuit_layers_proof_encoded is: {:?}",
      mem_circuit_layers_proof_encoded.len()
    );

    mem_circuit_layers_proof
  }

  fn verify(
    &self,
    num_cells: usize,
    num_ops: usize,
    comm: &AddrTimestampsCommitment,
    gens: &AddrTimestampsGens,
    comm_ops_val: &PolyCommitment,
    r: &Vec<Scalar>,
    r_hash: &Scalar,
    r_multiset_check: &Scalar,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(MemCircuitLayersProof::protocol_name());

    let eval_init = self.eval_init;
    let eval_read = self.eval_read;
    let eval_write = self.eval_write;
    let eval_audit = self.eval_audit;

    let start = Instant::now();
    eval_init.append_to_transcript(b"claim_eval_init", transcript);
    eval_read.append_to_transcript(b"claim_eval_read", transcript);
    eval_write.append_to_transcript(b"claim_eval_write", transcript);
    eval_audit.append_to_transcript(b"claim_eval_audit", transcript);

    // verify the multiset check
    assert_eq!(eval_init * eval_write, eval_read * eval_audit);

    let (claim_last_init, rand_init) = self
      .proof_prod_layer_init
      .verify(eval_init, num_cells, transcript);

    let (claim_last_read, rand_read) = self
      .proof_prod_layer_read
      .verify(eval_read, num_ops, transcript);

    let (claim_last_write, rand_write) = self
      .proof_prod_layer_write
      .verify(eval_write, num_ops, transcript);

    let (claim_last_audit, rand_audit) = self
      .proof_prod_layer_audit
      .verify(eval_audit, num_cells, transcript);
    let duration = start.elapsed();
    println!("Verifying product proof took {:?}", duration);

    let start = Instant::now();
    assert!(self
      .proof_hash_layer
      .verify(
        (&rand_init, &rand_read, &rand_write, &rand_audit),
        (
          &claim_last_init,
          &claim_last_read,
          &claim_last_write,
          &claim_last_audit,
        ),
        comm,
        gens,
        comm_ops_val,
        r,
        r_hash,
        r_multiset_check,
        transcript,
      )
      .is_ok());
    let duration = start.elapsed();
    println!("Verifying hash layer proof took {:?}", duration);

    Ok(())
  }
}

#[derive(Debug, Serialize, Deserialize)]
struct MemCircuitProof {
  proof_row: MemCircuitLayersProof,
  proof_col: MemCircuitLayersProof,
}

impl MemCircuitProof {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial memory circuit proof"
  }

  pub fn prove(
    mem_circuit: &mut MemCircuit,
    dense: &SparseMatPolynomialAsDense,
    comm_sparsepoly: &SparseMatPolyCommitment,
    gens: &SparseMatPolyCommitmentGens,
    transcript: &mut Transcript,
  ) -> Self {
    transcript.append_protocol_name(MemCircuitProof::protocol_name());

    // memory checking
    let proof_row = MemCircuitLayersProof::prove(
      &mut mem_circuit.row_layers,
      &dense.row,
      &comm_sparsepoly.comm_row,
      &gens.gens_row,
      transcript,
    );
    let proof_col = MemCircuitLayersProof::prove(
      &mut mem_circuit.col_layers,
      &dense.col,
      &comm_sparsepoly.comm_col,
      &gens.gens_col,
      transcript,
    );

    MemCircuitProof {
      proof_row,
      proof_col,
    }
  }

  pub fn verify(
    &self,
    comm: &SparseMatPolyCommitment,
    comm_values: &ValuesCommitment,
    gens: &SparseMatPolyCommitmentGens,
    rx: &Vec<Scalar>,
    ry: &Vec<Scalar>,
    r_hash: &Scalar,
    r_multiset_check: &Scalar,
    nz: usize,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(MemCircuitProof::protocol_name());

    let num_ops = nz.next_power_of_two();

    let rx_len = rx.len();
    let ry_len = ry.len();

    let num_cells_row = rx_len.pow2();
    let num_cells_col = ry_len.pow2();

    let start = Instant::now();
    assert!(self
      .proof_row
      .verify(
        num_cells_row,
        num_ops,
        &comm.comm_row,
        &gens.gens_row,
        &comm_values.comm_row_ops_val,
        rx,
        r_hash,
        r_multiset_check,
        transcript
      )
      .is_ok());
    assert!(self
      .proof_col
      .verify(
        num_cells_col,
        num_ops,
        &comm.comm_col,
        &gens.gens_col,
        &comm_values.comm_col_ops_val,
        ry,
        r_hash,
        r_multiset_check,
        transcript
      )
      .is_ok());

    let duration = start.elapsed();
    println!("Verify: proof_mem took {:?}", duration);

    Ok(())
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SparseMatPolyEvalProof {
  comm_values: ValuesCommitment,
  eval_circuit_proof: EvalCircuitProof,
  mem_circuit_proof: MemCircuitProof,
}

#[allow(dead_code)]
impl SparseMatPolyEvalProof {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial evaluation proof"
  }

  pub fn prove(
    _poly: &SparseMatPolynomial,
    comm: &SparseMatPolyCommitment,
    dense: &SparseMatPolynomialAsDense,
    rx: &Vec<Scalar>, // point at which the polynomial is evaluated
    ry: &Vec<Scalar>,
    eval_table_rx: &Vec<Scalar>,
    eval_table_ry: &Vec<Scalar>,
    eval: Scalar, // evaluation of \widetilde{M}(r = (rx,ry))
    gens: &SparseMatPolyCommitmentGens,
    transcript: &mut Transcript,
  ) -> SparseMatPolyEvalProof {
    transcript.append_protocol_name(SparseMatPolyEvalProof::protocol_name());

    let start = Instant::now();
    let values = dense.deref(eval_table_rx, eval_table_ry);
    let duration = start.elapsed();
    println!("Time to deref memory addresses {:?}", duration);

    // commit to non-deterministic choices of the prover i.e., eval_cicruit.poly_row_deref and eval_cicruit.poly_col_deref
    let start = Instant::now();
    let comm_values = values.commit(&gens.gens_row, &gens.gens_col);
    comm_values.append_to_transcript(b"comm_poly_row_col_ops_val", transcript);
    let duration = start.elapsed();
    println!("Time to commit to non-det values {:?}", duration);

    // produce a random element from the transcript for hash function
    let r_hash = transcript.challenge_scalar(b"challenge_r_hash");
    let r_multiset_check = transcript.challenge_scalar(b"challenge_r_multiset_check");

    let start = Instant::now();
    // build a network to evaluate the sparse polynomial
    let mut net = PolyEvalNetwork::new(
      dense,
      &values,
      rx,
      ry,
      &eval_table_rx,
      &eval_table_ry,
      &r_hash,
      &r_multiset_check,
    );
    debug_assert!(net.evaluate() == eval);

    let duration = start.elapsed();
    println!("Time to build the layered network is: {:?}", duration);

    let start = Instant::now();
    let eval_circuit_proof = EvalCircuitProof::prove(
      &mut net.eval_circuit,
      &values,
      &comm_values,
      &comm.comm_val,
      &gens.gens_val,
      &gens.gens_row.gens_ops,
      &eval,
      transcript,
    );
    let duration = start.elapsed();
    println!("Time to produce eval_circuit_proof {:?}", duration);

    let start = Instant::now();
    let mem_circuit_proof =
      MemCircuitProof::prove(&mut net.mem_circuit, &dense, comm, gens, transcript);
    let duration = start.elapsed();
    println!("Time to produce mem_circuit_proof {:?}", duration);

    SparseMatPolyEvalProof {
      comm_values,
      eval_circuit_proof,
      mem_circuit_proof,
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

    // add claims to transcript and obtain challenges for randomized mem-check circuit
    self
      .comm_values
      .append_to_transcript(b"comm_poly_row_col_ops_val", transcript);

    // produce a random element from the transcript for hash function
    let r_hash = transcript.challenge_scalar(b"challenge_r_hash");
    let r_multiset_check = transcript.challenge_scalar(b"challenge_r_multiset_check");

    assert!(self
      .eval_circuit_proof
      .verify(
        nz,
        &comm.comm_val,
        &gens.gens_val,
        &self.comm_values,
        &gens.gens_row.gens_ops,
        &gens.gens_col.gens_ops,
        eval,
        transcript,
      )
      .is_ok());

    assert!(self
      .mem_circuit_proof
      .verify(
        comm,
        &self.comm_values,
        gens,
        rx,
        ry,
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
      &poly_M,
      &poly_comm,
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
