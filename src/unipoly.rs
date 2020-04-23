use super::commitments::{Commitments, MultiCommitGens};
use super::scalar::{Scalar, ScalarFromPrimitives};
use super::transcript::{AppendToTranscript, ProofTranscript};
use curve25519_dalek::ristretto::RistrettoPoint;
use merlin::Transcript;
use serde::{Deserialize, Serialize};

// ax^2 + bx + c stored as vec![a,b,c]
// ax^3 + bx^2 + cx + d stored as vec![a,b,c,d]
#[derive(Debug)]
pub struct UniPoly {
  coeffs: Vec<Scalar>,
}

// ax^2 + bx + c stored as vec![a,c]
// ax^3 + bx^2 + cx + d stored as vec![a,c,d]
#[derive(Serialize, Deserialize, Debug)]
pub struct CompressedUniPoly {
  coeffs_except_linear_term: Vec<Scalar>,
}

impl UniPoly {
  pub fn from_evals(evals: &Vec<Scalar>) -> Self {
    // we only support degree-2 or degree-3 univariate polynomials
    assert!(evals.len() == 3 || evals.len() == 4);
    let coeffs = if evals.len() == 3 {
      // ax^2 + bx + c
      let two_inv = (2 as usize).to_scalar().invert().unwrap();

      let c = evals[0];
      let a = two_inv * (evals[2] - evals[1] - evals[1] + c);
      let b = evals[1] - c - a;
      vec![c, b, a]
    } else {
      // ax^3 + bx^2 + cx + d
      let two_inv = (2 as usize).to_scalar().invert().unwrap();
      let six_inv = (6 as usize).to_scalar().invert().unwrap();

      let d = evals[0];
      let a = six_inv
        * (evals[3] - evals[2] - evals[2] - evals[2] + evals[1] + evals[1] + evals[1] - evals[0]);
      let b = two_inv
        * (evals[0] + evals[0] - evals[1] - evals[1] - evals[1] - evals[1] - evals[1]
          + evals[2]
          + evals[2]
          + evals[2]
          + evals[2]
          - evals[3]);
      let c = evals[1] - d - a - b;
      vec![d, c, b, a]
    };

    UniPoly { coeffs }
  }

  pub fn degree(&self) -> usize {
    self.coeffs.len() - 1
  }

  pub fn as_vec(&self) -> Vec<Scalar> {
    self.coeffs.clone()
  }

  pub fn eval_at_zero(&self) -> Scalar {
    self.coeffs[0]
  }

  pub fn eval_at_one(&self) -> Scalar {
    (0..self.coeffs.len()).map(|i| self.coeffs[i]).sum()
  }

  pub fn evaluate(&self, r: &Scalar) -> Scalar {
    let mut eval = self.coeffs[0];
    let mut power = *r;
    for i in 1..self.coeffs.len() {
      eval = &eval + &power * &self.coeffs[i];
      power = &power * r;
    }
    eval
  }

  pub fn compress(&self) -> CompressedUniPoly {
    let coeffs_except_linear_term = [&self.coeffs[0..1], &self.coeffs[2..]].concat();
    assert_eq!(coeffs_except_linear_term.len() + 1, self.coeffs.len());
    CompressedUniPoly {
      coeffs_except_linear_term,
    }
  }

  pub fn commit(&self, gens: &MultiCommitGens, blind: &Scalar) -> RistrettoPoint {
    self.coeffs.commit(blind, gens)
  }
}

impl CompressedUniPoly {
  // we require eval(0) + eval(1) = hint, so we can solve for the linear term as:
  // linear_term = hint - 2 * constant_term - deg2 term - deg3 term
  pub fn decompress(&self, hint: &Scalar) -> UniPoly {
    let mut linear_term =
      hint - self.coeffs_except_linear_term[0] - self.coeffs_except_linear_term[0];
    for i in 1..self.coeffs_except_linear_term.len() {
      linear_term = linear_term - self.coeffs_except_linear_term[i];
    }

    let mut coeffs: Vec<Scalar> = Vec::new();
    coeffs.extend(vec![&self.coeffs_except_linear_term[0]]);
    coeffs.extend(vec![&linear_term]);
    coeffs.extend(self.coeffs_except_linear_term[1..].to_vec());
    assert_eq!(self.coeffs_except_linear_term.len() + 1, coeffs.len());
    UniPoly { coeffs }
  }
}

impl AppendToTranscript for UniPoly {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, b"UniPoly_begin");
    for i in 0..self.coeffs.len() {
      transcript.append_scalar(b"coeff", &self.coeffs[i]);
    }
    transcript.append_message(label, b"UniPoly_end");
  }
}

mod tests {
  #[cfg(test)]
  use super::*;

  #[test]
  fn test_from_evals_quad() {
    // polynomial is 2x^2 + 3x + 1
    let e0 = Scalar::one();
    let e1 = (6 as usize).to_scalar();
    let e2 = (15 as usize).to_scalar();
    let evals = vec![e0, e1, e2];
    let poly = UniPoly::from_evals(&evals);

    assert_eq!(poly.eval_at_zero(), e0);
    assert_eq!(poly.eval_at_one(), e1);
    assert_eq!(poly.coeffs.len(), 3);
    assert_eq!(poly.coeffs[0], Scalar::one());
    assert_eq!(poly.coeffs[1], (3 as usize).to_scalar());
    assert_eq!(poly.coeffs[2], (2 as usize).to_scalar());

    let hint = e0 + e1;
    let compressed_poly = poly.compress();
    let decompressed_poly = compressed_poly.decompress(&hint);
    for i in 0..decompressed_poly.coeffs.len() {
      assert_eq!(decompressed_poly.coeffs[i], poly.coeffs[i]);
    }

    let e3 = (28 as usize).to_scalar();
    assert_eq!(poly.evaluate(&(3 as usize).to_scalar()), e3);
  }

  #[test]
  fn test_from_evals_cubic() {
    // polynomial is x^3 + 2x^2 + 3x + 1
    let e0 = Scalar::one();
    let e1 = (7 as usize).to_scalar();
    let e2 = (23 as usize).to_scalar();
    let e3 = (55 as usize).to_scalar();
    let evals = vec![e0, e1, e2, e3];
    let poly = UniPoly::from_evals(&evals);

    assert_eq!(poly.eval_at_zero(), e0);
    assert_eq!(poly.eval_at_one(), e1);
    assert_eq!(poly.coeffs.len(), 4);
    assert_eq!(poly.coeffs[0], Scalar::one());
    assert_eq!(poly.coeffs[1], (3 as usize).to_scalar());
    assert_eq!(poly.coeffs[2], (2 as usize).to_scalar());
    assert_eq!(poly.coeffs[3], (1 as usize).to_scalar());

    let hint = e0 + e1;
    let compressed_poly = poly.compress();
    let decompressed_poly = compressed_poly.decompress(&hint);
    for i in 0..decompressed_poly.coeffs.len() {
      assert_eq!(decompressed_poly.coeffs[i], poly.coeffs[i]);
    }

    let e4 = (109 as usize).to_scalar();
    assert_eq!(poly.evaluate(&(4 as usize).to_scalar()), e4);
  }
}
