#[allow(dead_code)]
use super::dense_mlpoly::DensePolynomial;
use super::dense_mlpoly::{
  DensePolynomialSize, DensePolynomialTrait, EqPolynomial, PolyCommitment, PolyCommitmentBlinds,
  PolyCommitmentGens, PolyEvalProof,
};
use super::errors::ProofVerifyError;
use super::math::Math;
use super::scalar::Scalar;
//use super::scalar::ScalarFromPrimitives;
use super::sumcheck::SumcheckInstanceProof;
use super::transcript::{AppendToTranscript, ProofTranscript};
use super::unipoly::SumcheckProofPolyABI;
use super::unipoly::{CubicPoly, QuadPoly};
use curve25519_dalek::ristretto::CompressedRistretto;
use merlin::Transcript;
use rand::rngs::OsRng;
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
  dense_M: Vec<bool>,
  dense_vals: Vec<Scalar>,
}

pub struct SparseMatPolynomialSize {
  dense_M_size: DensePolynomialSize,
  dense_vals_size: DensePolynomialSize,
}

pub struct SparseMatPolyCommitmentGens {
  gens_M: PolyCommitmentGens,
  gens_vals: PolyCommitmentGens,
}

impl SparseMatPolyCommitmentGens {
  pub fn new(size: &SparseMatPolynomialSize, label: &'static [u8]) -> SparseMatPolyCommitmentGens {
    let gens_M = PolyCommitmentGens::new(&size.dense_M_size, label);
    let gens_vals = PolyCommitmentGens::new(&size.dense_vals_size, label);
    SparseMatPolyCommitmentGens { gens_M, gens_vals }
  }
}

pub struct SparseMatPolyCommitmentBlinds {
  blinds_M: PolyCommitmentBlinds,
  blinds_vals: PolyCommitmentBlinds,
}

impl SparseMatPolyCommitmentBlinds {
  pub fn new(size: &SparseMatPolynomialSize, csprng: &mut OsRng) -> SparseMatPolyCommitmentBlinds {
    let blinds_M = PolyCommitmentBlinds::new(&size.dense_M_size, csprng);
    let blinds_vals = PolyCommitmentBlinds::new(&size.dense_vals_size, csprng);
    SparseMatPolyCommitmentBlinds {
      blinds_M,
      blinds_vals,
    }
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SparseMatPolyCommitment {
  comm_M: PolyCommitment,
  comm_vals: PolyCommitment,
}

impl SparseMatPolynomial {
  fn sparse_to_dense_rep(
    num_vars_x: usize,
    num_vars_y: usize,
    M: &Vec<SparseMatEntry>,
  ) -> (Vec<bool>, Vec<Scalar>) {
    // we ensure the total number of bits is a power-of-two
    let num_bits = num_vars_x + num_vars_y;
    let mut num_bits_ext = num_bits.next_power_of_two();
    if num_bits_ext.log2() % 2 != 0 {
      // TODO: avoid doing this padding
      num_bits_ext = num_bits_ext * 2;
    }

    let extra_bits = num_bits_ext - num_bits;

    let N = M.len().next_power_of_two();
    let ell = num_bits_ext;
    let len = N * ell;
    let mut bits: Vec<bool> = vec![false; len];
    let mut vals: Vec<Scalar> = vec![Scalar::zero(); N];

    for i in 0..M.len() {
      let row = M[i].row;
      let col = M[i].col;
      let bits_row = row.get_bits(num_vars_x);
      let bits_col = col.get_bits(num_vars_y + extra_bits);
      for j in 0..bits_row.len() {
        bits[j * N + i] = bits_row[j];
      }
      for k in 0..bits_col.len() {
        bits[(bits_row.len() + k) * N + i] = bits_col[k];
      }
      vals[i] = M[i].val;
    }

    (bits, vals)
  }

  pub fn new(num_vars_x: usize, num_vars_y: usize, M: Vec<SparseMatEntry>) -> Self {
    let (dense_M, dense_vals) =
      SparseMatPolynomial::sparse_to_dense_rep(num_vars_x, num_vars_y, &M);
    SparseMatPolynomial {
      num_vars_x,
      num_vars_y,
      M,
      dense_M,
      dense_vals,
    }
  }

  pub fn size(&self) -> SparseMatPolynomialSize {
    let (dense_M, dense_vals) = self.dense_rep();
    let poly_M = DensePolynomial::<bool>::new(dense_M);
    let poly_vals = DensePolynomial::<Scalar>::new(dense_vals);
    SparseMatPolynomialSize {
      dense_M_size: poly_M.size(),
      dense_vals_size: poly_vals.size(),
    }
  }

  pub fn get_num_nz_entries(&self) -> usize {
    self.dense_vals.len()
  }

  pub fn dense_rep(&self) -> (Vec<bool>, Vec<Scalar>) {
    (self.dense_M.clone(), self.dense_vals.clone())
  }

  pub fn evaluate_with_tables(
    &self,
    eval_table_rx: &Vec<Scalar>,
    eval_table_ry: &Vec<Scalar>,
  ) -> Scalar {
    assert_eq!(self.num_vars_x.pow2(), eval_table_rx.len());
    assert_eq!(self.num_vars_y.pow2(), eval_table_ry.len());

    (0..self.M.len())
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| {
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
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| {
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
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| {
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
    blinds: &SparseMatPolyCommitmentBlinds,
    gens: &SparseMatPolyCommitmentGens,
  ) -> SparseMatPolyCommitment {
    let (dense_M, dense_vals) = self.dense_rep();
    let poly_M = DensePolynomial::<bool>::new(dense_M);
    let poly_vals = DensePolynomial::<Scalar>::new(dense_vals);

    SparseMatPolyCommitment {
      comm_M: poly_M.commit(&blinds.blinds_M, &gens.gens_M),
      comm_vals: poly_vals.commit(&blinds.blinds_vals, &gens.gens_vals),
    }
  }
}

#[derive(Debug)]
struct Layer<T> {
  vec: DensePolynomial<T>,
}

#[derive(Debug)]
struct PolyEvalNetwork {
  r: Vec<Scalar>,
  input_layer: Layer<bool>,
  r_layer: Layer<Scalar>,
  product_layers_left: Vec<Layer<Scalar>>,
  product_layers_right: Vec<Layer<Scalar>>,
  dotp_layer: Layer<Scalar>,
  vals_layer: Layer<Scalar>,
}

impl PolyEvalNetwork {
  fn compute_r_layer(M_bits: &Vec<bool>, r: &Vec<Scalar>) -> Layer<Scalar> {
    let N = M_bits.len() / r.len();

    let one = Scalar::one();
    let one_minus_r = (0..r.len())
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| &one - &r[i])
      .collect::<Vec<Scalar>>();

    let M_bits_r = (0..M_bits.len())
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| {
        if M_bits[i] {
          r[i / N]
        } else {
          one_minus_r[i / N]
        }
      })
      .collect::<Vec<Scalar>>();

    Layer {
      vec: DensePolynomial::new(M_bits_r),
    }
  }

  fn compute_product_layer(
    inp_left: &Layer<Scalar>,
    inp_right: &Layer<Scalar>,
  ) -> (Layer<Scalar>, Layer<Scalar>) {
    let len = inp_left.vec.len() + inp_right.vec.len();
    let left_vec = (0..len / 4)
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| &inp_left.vec[i] * &inp_right.vec[i])
      .collect::<Vec<Scalar>>();
    let right_vec = (len / 4..len / 2)
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| &inp_left.vec[i] * &inp_right.vec[i])
      .collect::<Vec<Scalar>>();

    (
      Layer {
        vec: DensePolynomial::new(left_vec),
      },
      Layer {
        vec: DensePolynomial::new(right_vec),
      },
    )
  }

  pub fn build(poly: &SparseMatPolynomial, rx: &Vec<Scalar>, ry: &Vec<Scalar>) -> Self {
    assert_eq!(rx.len(), poly.num_vars_x);
    assert_eq!(ry.len(), poly.num_vars_y);

    let start = Instant::now();
    let (evals_M_bits, evals_M_vals) = poly.dense_rep();
    println!(
      "Length of eval_M_bits is {} and eval_M_vals is {}",
      evals_M_bits.len(),
      evals_M_vals.len(),
    );
    let duration = start.elapsed();
    println!(
      "Time spent in obtaining a dense representation {:?}",
      duration
    );

    // pad the vector with zeros so it is a perfect power of two
    let mut num_rs = (rx.len() + ry.len()).next_power_of_two();
    if num_rs.log2() % 2 != 0 {
      // TODO: avoid this padding
      num_rs = num_rs * 2;
    }
    let mut r = rx.clone();
    r.extend(vec![Scalar::zero(); num_rs - (rx.len() + ry.len())]);
    r.extend(ry);

    let start = Instant::now();
    // in the first stage, we multiply all vectors with contributions from r
    let r_layer = PolyEvalNetwork::compute_r_layer(&evals_M_bits, &r);
    let duration = start.elapsed();
    println!("Time spent in building the r layer {:?}", duration);

    // binary tree of product gates
    let start = Instant::now();
    let mut layers_left: Vec<Layer<Scalar>> = Vec::new();
    let mut layers_right: Vec<Layer<Scalar>> = Vec::new();
    let (poly_left, poly_right) = r_layer.vec.split(evals_M_bits.len() / 2);
    layers_left.push(Layer { vec: poly_left });
    layers_right.push(Layer { vec: poly_right });
    let num_layers = r.len().log2();
    for i in 0..num_layers {
      let (outp_left, outp_right) =
        PolyEvalNetwork::compute_product_layer(&layers_left[i], &layers_right[i]);

      layers_left.push(outp_left);
      layers_right.push(outp_right);
    }

    let (mut last_layer_left, last_layer_right) = (
      layers_left.pop().unwrap().vec,
      layers_right.pop().unwrap().vec,
    );
    last_layer_left.extend(&last_layer_right);
    let duration = start.elapsed();
    println!("Time spent in building the product layer {:?}", duration);

    let input_layer = Layer {
      vec: DensePolynomial::new(evals_M_bits),
    };
    let vals_layer = Layer {
      vec: DensePolynomial::new(evals_M_vals),
    };

    PolyEvalNetwork {
      r,
      input_layer,
      r_layer,
      product_layers_left: layers_left,
      product_layers_right: layers_right,
      dotp_layer: Layer {
        vec: last_layer_left,
      },
      vals_layer,
    }
  }

  pub fn evaluate(&self) -> Scalar {
    self.dotp_layer.vec.dotproduct(&self.vals_layer.vec)
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

#[allow(dead_code)]
#[derive(Debug, Serialize, Deserialize)]
pub struct SparseMatPolyEvalProof {
  proof_dotp_layer: LayerProof<QuadPoly>,
  proof_vals: PolyEvalProof,
  comm_vals: CompressedRistretto, // TODO: remove this
  proof_product_layers: Vec<LayerProof<CubicPoly>>,
  proof_input_layer_one: LayerProof<QuadPoly>,
  proof_input_layer_two: LayerProof<CubicPoly>,
  proof_dense_bits: PolyEvalProof,
  comm_dense_bits: CompressedRistretto, // TODO: remove this
}

#[allow(dead_code)]
impl SparseMatPolyEvalProof {
  fn protocol_name() -> &'static [u8] {
    b"Sparse polynomial evaluation proof"
  }

  pub fn prove(
    poly_M: &SparseMatPolynomial,
    comm: &SparseMatPolyCommitment,
    blinds: &SparseMatPolyCommitmentBlinds,
    rx: &Vec<Scalar>, // point at which the polynomial is evaluated
    ry: &Vec<Scalar>,
    eval: Scalar, // evaluation of \widetilde{M}(r = (rx,ry))
    gens: &SparseMatPolyCommitmentGens,
    transcript: &mut Transcript,
  ) -> SparseMatPolyEvalProof {
    transcript.append_protocol_name(SparseMatPolyEvalProof::protocol_name());

    let start = Instant::now();
    // build a network to evaluate the sparse polynomial
    let mut net = PolyEvalNetwork::build(&poly_M, &rx, &ry);
    debug_assert!(net.evaluate() == eval);

    //let claim_network_eval = net.evaluate();
    let claim_network_eval = eval;
    let duration = start.elapsed();
    println!(
      "Time elapsed in evaluating polynomial using layered network is: {:?}",
      duration
    );

    let n = net.dotp_layer.vec.len(); //size of vectors in the product layers
    let ell = net.r.len(); //size of r
    let num_layers = net.product_layers_left.len();

    // dot product layer
    let start = Instant::now();
    let poly_vals = net.vals_layer.vec.clone();
    let num_rounds_dotp = net.dotp_layer.vec.len().log2();
    let comb_func_dotp =
      |poly_A_comp: &Scalar, poly_B_comp: &Scalar| -> Scalar { poly_A_comp * poly_B_comp };
    let (sc_proof_dotp_layer, r_dotp_layer, claims_dotp_layer) =
      SumcheckInstanceProof::<QuadPoly>::prove(
        &claim_network_eval,
        num_rounds_dotp,
        &mut net.dotp_layer.vec,
        &mut net.vals_layer.vec,
        comb_func_dotp,
        transcript,
      );
    transcript.append_scalar(b"claim_chis", &claims_dotp_layer[0]);
    transcript.append_scalar(b"claim_vals", &claims_dotp_layer[1]);
    let duration = start.elapsed();
    println!("Time elapsed in the dot product layer: {:?}", duration);

    // prove claim_vals using the dense polynomial commitment scheme
    let start = Instant::now();
    assert_eq!(poly_vals.evaluate(&r_dotp_layer), claims_dotp_layer[1]);
    let (proof_vals, comm_vals) = PolyEvalProof::prove(
      &poly_vals,
      &comm.comm_vals,
      &blinds.blinds_vals,
      &r_dotp_layer,
      claims_dotp_layer[1],
      &gens.gens_vals,
      transcript,
    );
    let duration = start.elapsed();
    println!(
      "Time elapsed in the dot product polydecommit: {:?}",
      duration
    );

    // product layers
    let mut rand = r_dotp_layer;
    let mut claim = claims_dotp_layer[0];

    let proof_dotp_layer = LayerProof {
      proof: sc_proof_dotp_layer,
      claims: claims_dotp_layer,
    };

    let start = Instant::now();
    let mut proof_product_layers: Vec<LayerProof<CubicPoly>> = Vec::new();
    for layer_id in (0..num_layers).rev() {
      let len =
        net.product_layers_left[layer_id].vec.len() + net.product_layers_right[layer_id].vec.len();

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
        &mut net.product_layers_left[layer_id].vec,
        &mut net.product_layers_right[layer_id].vec,
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

      proof_product_layers.push(LayerProof {
        proof: proof_prod,
        claims: claims_prod[0..claims_prod.len() - 1].to_vec(),
      });
    }
    let duration = start.elapsed();
    println!("Time elapsed in the product layers: {:?}", duration);

    // input layer
    let start = Instant::now();
    let poly_M_bits = net.input_layer.vec.clone();

    // we will execute the sum-check in two phases
    let r1 = rand[0..ell.log2()].to_vec(); //r1 is of size log(ell)
    let r2 = rand[ell.log2()..].to_vec(); //r2 is of size log(n)
    assert_eq!(r1.len(), ell.log2());
    assert_eq!(r2.len(), n.log2());

    let mut poly_A = DensePolynomial::new(EqPolynomial::new(r2.clone()).evals());
    let evals_r1 = EqPolynomial::new(r1.clone()).evals();
    let mut poly_B = DensePolynomial::new({
      let mut evals_H: Vec<Scalar> = vec![Scalar::zero(); n];
      for i in 0..ell {
        let weight = evals_r1[i];
        for j in 0..n {
          evals_H[j] = evals_H[j] + net.r_layer.vec[i * n + j] * weight;
        }
      }
      evals_H
    });
    let num_rounds_input_one = n.log2();
    let comb_func_input_one =
      |poly_A_comp: &Scalar, poly_B_comp: &Scalar| -> Scalar { poly_A_comp * poly_B_comp };
    let (proof_input_one, rand_input_one, claims_input_one) =
      SumcheckInstanceProof::<QuadPoly>::prove(
        &claim,
        num_rounds_input_one,
        &mut poly_A,
        &mut poly_B,
        comb_func_input_one,
        transcript,
      );
    transcript.append_scalar(b"claim_input_right", &claims_input_one[1]);
    let proof_input_layer_one = LayerProof {
      proof: proof_input_one,
      claims: claims_input_one[1..claims_input_one.len()].to_vec(),
    };

    // second sum-check for input layer
    let num_rounds_input_two = ell.log2();
    let claim = claims_input_one[1];
    //let comb_func_input_two =
    //  |poly_A_comp: &Scalar, poly_B_comp: &Scalar, poly_C_comp: &Scalar| -> Scalar {
    //    (poly_A_comp * poly_B_comp + (Scalar::one() - poly_A_comp) * (Scalar::one() - poly_B_comp))
    //      * poly_C_comp
    //  };

    let comb_func_input_two =
      |poly_A_comp: &Scalar, poly_B_comp: &Scalar, poly_C_comp: &Scalar| -> Scalar {
        let prod = poly_A_comp * poly_B_comp;
        (&prod + &prod + &Scalar::one() - poly_A_comp - poly_B_comp) * poly_C_comp
      };

    let mut poly_A = {
      // bound input layer with randomness from the first sum-check
      let poly_A_decomposed = net.input_layer.vec;
      let r = rand_input_one[rand_input_one.len() - 1];

      let mut poly_A_decomposed_scalar = poly_A_decomposed.bound_poly_var_bot(&r);

      for j in (0..rand_input_one.len() - 1).rev() {
        poly_A_decomposed_scalar.bound_poly_var_bot(&rand_input_one[j]);
      }
      poly_A_decomposed_scalar
    };
    let mut poly_B = DensePolynomial::new(net.r);
    let mut poly_C = DensePolynomial::new(evals_r1);
    let (proof_input_two, rand_input_two, claims_input_two) =
      SumcheckInstanceProof::<CubicPoly>::prove(
        &claim,
        num_rounds_input_two,
        &mut poly_A,
        &mut poly_B,
        &mut poly_C,
        comb_func_input_two,
        transcript,
      );

    let proof_input_layer_two = LayerProof {
      proof: proof_input_two,
      claims: claims_input_two[0..claims_input_two.len() - 2].to_vec(),
    };
    transcript.append_scalar(b"claim_input_left", &claims_input_two[0]);

    let duration = start.elapsed();
    println!("Time elapsed in the input layer: {:?}", duration);

    let start = Instant::now();
    // prove claim_input_left using the dense polynomial commitment scheme
    let mut rand = rand_input_two.clone();
    rand.extend(&rand_input_one);
    let (proof_dense_bits, comm_dense_bits) = PolyEvalProof::prove(
      &poly_M_bits,
      &comm.comm_M,
      &blinds.blinds_M,
      &rand,
      claims_input_two[0],
      &gens.gens_M,
      transcript,
    );
    let duration = start.elapsed();
    println!("Time elapsed in the polydecommit of M_bits: {:?}", duration);

    SparseMatPolyEvalProof {
      proof_dotp_layer,
      proof_vals,
      comm_vals,
      proof_product_layers,
      proof_input_layer_one,
      proof_input_layer_two,
      proof_dense_bits,
      comm_dense_bits,
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
    transcript.append_protocol_name(SparseMatPolyEvalProof::protocol_name());

    let mut num_rs = (rx.len() + ry.len()).next_power_of_two();
    if num_rs.log2() % 2 != 0 {
      // TODO: avoid this padding
      num_rs = num_rs * 2;
    }
    let mut r = rx.clone();
    r.extend(vec![Scalar::zero(); num_rs - (rx.len() + ry.len())]);
    r.extend(ry);

    let mut num_rounds = nz.next_power_of_two().log2();
    let (claim_dotp, r_dotp) = self.proof_dotp_layer.verify(eval, num_rounds, transcript);
    assert_eq!(
      claim_dotp,
      self.proof_dotp_layer.claims[0] * self.proof_dotp_layer.claims[1]
    );

    transcript.append_scalar(b"claim_chis", &self.proof_dotp_layer.claims[0]);
    transcript.append_scalar(b"claim_vals", &self.proof_dotp_layer.claims[1]);

    //verify self.proof_dotp_layer.claims[1] through polycommit scheme
    assert!(self
      .proof_vals
      .verify(
        &gens.gens_vals,
        transcript,
        &r_dotp,
        self.comm_vals,
        &comm.comm_vals,
      )
      .is_ok());

    let num_layers = r.len().next_power_of_two().log2();
    let mut claim = self.proof_dotp_layer.claims[0];
    let mut rand = r_dotp;
    for i in 0..num_layers {
      let (claim_last, rand_prod) =
        self.proof_product_layers[i].verify(claim, num_rounds, transcript);

      let claims_prod = &self.proof_product_layers[i].claims;
      transcript.append_scalar(b"claim_prod_left", &claims_prod[0]);
      transcript.append_scalar(b"claim_prod_right", &claims_prod[1]);

      assert_eq!(rand.len(), rand_prod.len());
      let eq: Scalar = (0..rand.len())
        .collect::<Vec<usize>>()
        .iter()
        .map(|&i| {
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

    let n = nz.next_power_of_two();
    let ell = r.len();
    let r1 = rand[0..ell.log2()].to_vec(); //r1 is of size log(ell)
    let r2 = rand[ell.log2()..].to_vec(); //r2 is of size log(n)
    assert_eq!(r1.len(), ell.log2());
    assert_eq!(r2.len(), n.log2());

    let (claim_last_one, rand_input_one) =
      self
        .proof_input_layer_one
        .verify(claim, n.log2(), transcript);
    let claims_input_one = &self.proof_input_layer_one.claims;
    transcript.append_scalar(b"claim_input_right", &claims_input_one[0]);
    // verify the last step of the sum-check one
    let term_left: Scalar = (0..r2.len())
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| {
        r2[i] * rand_input_one[i] + (Scalar::one() - r2[i]) * (Scalar::one() - rand_input_one[i])
      })
      .product();
    assert_eq!(term_left * claims_input_one[0], claim_last_one);

    let claim = claims_input_one[0];
    let (claim_last_two, rand_input_two) =
      self
        .proof_input_layer_two
        .verify(claim, ell.log2(), transcript);
    // verify the last step of the sum-check two
    let claims_input_two = &self.proof_input_layer_two.claims;
    transcript.append_scalar(b"claim_input_left", &claims_input_two[0]);

    let mut r_copy = DensePolynomial::new(r.clone());
    for i in 0..num_layers {
      r_copy.bound_poly_var_top(&rand_input_two[i]);
    }

    let eq: Scalar = (0..r1.len())
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| {
        r1[i] * rand_input_two[i] + (Scalar::one() - r1[i]) * (Scalar::one() - rand_input_two[i])
      })
      .product();
    assert_eq!(
      (claims_input_two[0] * r_copy[0]
        + (Scalar::one() - claims_input_two[0]) * (Scalar::one() - r_copy[0]))
        * eq,
      claim_last_two
    );

    let start = Instant::now();
    // verify claims_input[0] using poly decommit
    let mut rand = rand_input_two.clone();
    rand.extend(&rand_input_one);
    assert!(self
      .proof_dense_bits
      .verify(
        &gens.gens_M,
        transcript,
        &rand,
        self.comm_dense_bits,
        &comm.comm_M,
      )
      .is_ok());
    let duration = start.elapsed();
    println!("Verify: decommit M_bits took {:?}", duration);

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
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| {
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
    let blinds = SparseMatPolyCommitmentBlinds::new(&poly_M_size, &mut csprng);

    // commitment
    let poly_comm = poly_M.commit(&blinds, &gens);

    // evaluation
    let rx: Vec<Scalar> = (0..num_vars_x)
      .collect::<Vec<usize>>()
      .iter()
      .map(|&_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    let ry: Vec<Scalar> = (0..num_vars_y)
      .collect::<Vec<usize>>()
      .iter()
      .map(|&_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    let eval = poly_M.evaluate(&rx, &ry);

    let mut prover_transcript = Transcript::new(b"example");

    let proof = SparseMatPolyEvalProof::prove(
      &poly_M,
      &poly_comm,
      &blinds,
      &rx,
      &ry,
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
