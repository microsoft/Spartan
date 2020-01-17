#[allow(dead_code)]
use super::dense_mlpoly::DensePolynomial;
use super::dense_mlpoly::EqPolynomial;
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

#[allow(dead_code)]
#[derive(Debug, Serialize, Deserialize)]
pub struct LayerProofBatched<T: SumcheckProofPolyABI + AppendToTranscript> {
  pub proof: SumcheckInstanceProof<T>,
  pub claims_left: Vec<Scalar>,
  pub claims_right: Vec<Scalar>,
}

#[allow(dead_code)]
impl<T: SumcheckProofPolyABI + AppendToTranscript> LayerProofBatched<T> {
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

#[derive(Debug, Serialize, Deserialize)]
pub struct ProductCircuitEvalProofBatched {
  proof: Vec<LayerProofBatched<CubicPoly>>,
}

impl ProductCircuitEvalProof {
  #![allow(dead_code)]
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

impl ProductCircuitEvalProofBatched {
  pub fn prove(
    circuit_vec: &mut Vec<&mut ProductCircuit>,
    transcript: &mut Transcript,
  ) -> (Self, Vec<Scalar>) {
    assert!(circuit_vec.len() > 0);

    let mut proof: Vec<LayerProofBatched<CubicPoly>> = Vec::new();
    let num_layers = circuit_vec[0].left_vec.len();
    let mut claims_to_verify = (0..circuit_vec.len())
      .map(|i| circuit_vec[i].evaluate())
      .collect::<Vec<Scalar>>();
    let mut rand = Vec::new();
    for layer_id in (0..num_layers).rev() {
      // produce a fresh set of coeffs and a joint claim
      let coeff_vec = transcript.challenge_vector(b"rand_coeffs_next_layer", circuit_vec.len());
      let claim = (0..circuit_vec.len())
        .map(|i| claims_to_verify[i] * coeff_vec[i])
        .sum();

      let len = circuit_vec[0].left_vec[layer_id].len() + circuit_vec[0].right_vec[layer_id].len();

      let mut poly_C = DensePolynomial::new(EqPolynomial::new(rand.clone()).evals());
      assert_eq!(poly_C.len(), len / 2);

      let num_rounds_prod = poly_C.len().log2();
      let comb_func_prod = |poly_A_comp: &Scalar,
                            poly_B_comp: &Scalar,
                            poly_C_comp: &Scalar|
       -> Scalar { poly_A_comp * poly_B_comp * poly_C_comp };

      let mut poly_A_batched: Vec<&mut DensePolynomial> = Vec::new();
      let mut poly_B_batched: Vec<&mut DensePolynomial> = Vec::new();
      for prod_circuit in circuit_vec.iter_mut() {
        poly_A_batched.push(&mut prod_circuit.left_vec[layer_id]);
        poly_B_batched.push(&mut prod_circuit.right_vec[layer_id])
      }

      let (proof_prod, rand_prod, claims_prod) = SumcheckInstanceProof::<CubicPoly>::prove_batched(
        &claim,
        num_rounds_prod,
        &mut poly_A_batched,
        &mut poly_B_batched,
        &mut poly_C,
        &coeff_vec,
        comb_func_prod,
        transcript,
      );

      let (claims_prod_left, claims_prod_right, _claims_prod_eq) = claims_prod;

      for i in 0..circuit_vec.len() {
        transcript.append_scalar(b"claim_prod_left", &claims_prod_left[i]);
        transcript.append_scalar(b"claim_prod_right", &claims_prod_right[i]);
      }

      // produce a random challenge to condense two claims into a single claim
      let r_layer = transcript.challenge_scalar(b"challenge_r_layer");

      claims_to_verify = (0..circuit_vec.len())
        .map(|i| &claims_prod_left[i] + &r_layer * (&claims_prod_right[i] - &claims_prod_left[i]))
        .collect::<Vec<Scalar>>();

      let mut ext = vec![r_layer];
      ext.extend(rand_prod);
      rand = ext;

      proof.push(LayerProofBatched {
        proof: proof_prod,
        claims_left: claims_prod_left,
        claims_right: claims_prod_right,
      });
    }

    (ProductCircuitEvalProofBatched { proof }, rand)
  }

  pub fn verify(
    &self,
    claims_vec: &Vec<Scalar>,
    len: usize,
    transcript: &mut Transcript,
  ) -> (Vec<Scalar>, Vec<Scalar>) {
    let num_instances = claims_vec.len();

    let mut claims_to_verify = claims_vec.clone();

    let num_layers = len.log2();
    let mut rand: Vec<Scalar> = Vec::new();
    let mut num_rounds = 0;
    assert_eq!(self.proof.len(), num_layers);
    for i in 0..num_layers {
      // produce random coefficients, one for each instance
      let coeff_vec = transcript.challenge_vector(b"rand_coeffs_next_layer", num_instances);

      // produce a joint claim
      let claim = (0..num_instances)
        .map(|i| claims_to_verify[i] * coeff_vec[i])
        .sum();

      let (claim_last, rand_prod) = self.proof[i].verify(claim, num_rounds, transcript);

      let claims_prod_left = &self.proof[i].claims_left;
      let claims_prod_right = &self.proof[i].claims_right;
      assert_eq!(claims_prod_left.len(), num_instances);
      assert_eq!(claims_prod_right.len(), num_instances);

      for i in 0..num_instances {
        transcript.append_scalar(b"claim_prod_left", &claims_prod_left[i]);
        transcript.append_scalar(b"claim_prod_right", &claims_prod_right[i]);
      }

      assert_eq!(rand.len(), rand_prod.len());
      let eq: Scalar = (0..rand.len())
        .map(|i| {
          rand[i] * rand_prod[i] + (Scalar::one() - rand[i]) * (Scalar::one() - rand_prod[i])
        })
        .product();

      let claim_expected: Scalar = (0..num_instances)
        .map(|i| coeff_vec[i] * (claims_prod_left[i] * claims_prod_right[i] * eq))
        .sum();

      assert_eq!(claim_expected, claim_last);

      // produce a random challenge
      let r_layer = transcript.challenge_scalar(b"challenge_r_layer");

      claims_to_verify = (0..num_instances)
        .map(|i| &claims_prod_left[i] + &r_layer * (&claims_prod_right[i] - &claims_prod_left[i]))
        .collect::<Vec<Scalar>>();

      num_rounds = num_rounds + 1;
      let mut ext = vec![r_layer];
      ext.extend(rand_prod);
      rand = ext;
    }
    (claims_to_verify, rand)
  }
}
