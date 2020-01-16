#[allow(dead_code)]
use super::dense_mlpoly::DensePolynomial;
use super::dense_mlpoly::{
  EqPolynomial
};
use super::math::Math;
use super::scalar::Scalar;
use super::sumcheck::SumcheckInstanceProof;
use super::transcript::{AppendToTranscript, ProofTranscript};
use super::unipoly::CubicPoly;
use super::unipoly::SumcheckProofPolyABI;
use merlin::Transcript;
use serde::{Deserialize, Serialize};

#[derive(Debug)]
pub struct ProductCircuit {
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
pub struct LayerProof<T: SumcheckProofPolyABI + AppendToTranscript> {
  pub proof: SumcheckInstanceProof<T>,
  pub claims: Vec<Scalar>,
}

#[allow(dead_code)]
impl<T: SumcheckProofPolyABI + AppendToTranscript> LayerProof<T> {
  pub fn verify(
    &self,
    claim: Scalar,
    num_rounds: usize,
    transcript: &mut Transcript,
  ) -> (Scalar, Vec<Scalar>) {
    self.proof.verify(claim, num_rounds, transcript).unwrap()
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ProductCircuitEvalProof {
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
