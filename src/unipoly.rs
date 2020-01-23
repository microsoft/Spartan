use super::scalar::Scalar;
use super::scalar::ScalarFromPrimitives;
use super::transcript::{AppendToTranscript, ProofTranscript};
use merlin::Transcript;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct QuadPoly {
  eval_0: Scalar,
  eval_2: Scalar,
}

impl QuadPoly {
  pub fn new(eval_0: Scalar, eval_2: Scalar) -> Self {
    QuadPoly { eval_0, eval_2 }
  }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct CubicPoly {
  eval_0: Scalar,
  eval_2: Scalar,
  eval_3: Scalar,
}

#[allow(dead_code)]
impl CubicPoly {
  pub fn new(eval_0: Scalar, eval_2: Scalar, eval_3: Scalar) -> Self {
    CubicPoly {
      eval_0,
      eval_2,
      eval_3,
    }
  }
}

pub trait SumcheckProofPolyABI {
  fn eval_at_zero(&self) -> Scalar;
  //fn eval_at_one(&self) -> Scalar;
  fn evaluate(&self, r: &Scalar, e: &Scalar) -> Scalar;
}

impl SumcheckProofPolyABI for QuadPoly {
  fn eval_at_zero(&self) -> Scalar {
    self.eval_0
  }

  /*fn eval_at_one(&self) -> Scalar {
    self.eval_1
  }*/

  fn evaluate(&self, r: &Scalar, e: &Scalar) -> Scalar {
    let eval_1 = e - &self.eval_at_zero();

    // evaluate the claimed degree-2 polynomial at r
    let two_inv = (2 as usize).to_scalar().invert().unwrap();
    let rk_1 = r - Scalar::one();
    let rk_2 = r - (2 as usize).to_scalar();

    two_inv * rk_2 * rk_1 * self.eval_0 - rk_2 * r * eval_1 + two_inv * r * rk_1 * self.eval_2
  }
}

impl AppendToTranscript for QuadPoly {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, b"QuadPoly_begin");
    transcript.append_scalar(b"eval_0", &self.eval_0);
    //transcript.append_scalar(b"eval_1", &self.eval_1);
    transcript.append_scalar(b"eval_2", &self.eval_2);
    transcript.append_message(label, b"QuadPoly_end");
  }
}

impl SumcheckProofPolyABI for CubicPoly {
  fn eval_at_zero(&self) -> Scalar {
    self.eval_0
  }

  /*fn eval_at_one(&self) -> Scalar {
    self.eval_1
  }*/

  fn evaluate(&self, r: &Scalar, e: &Scalar) -> Scalar {
    let eval_1 = e - &self.eval_at_zero();

    // evaluate the claimed degree-3 polynomial at r
    let inv_6 = (6 as usize).to_scalar().invert().unwrap();
    let inv_2 = (2 as usize).to_scalar().invert().unwrap();

    let r_minus_1 = r - Scalar::one();
    let r_minus_2 = r - (2 as usize).to_scalar();
    let r_minus_3 = r - (3 as usize).to_scalar();

    -(inv_6 * r_minus_1 * r_minus_2 * r_minus_3 * self.eval_0)
      + (inv_2 * r * r_minus_2 * r_minus_3 * eval_1)
      - (inv_2 * r * r_minus_1 * r_minus_3 * self.eval_2)
      + (inv_6 * r * r_minus_1 * r_minus_2 * self.eval_3)
  }
}

impl AppendToTranscript for CubicPoly {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, b"CubicPoly_begin");
    transcript.append_scalar(b"eval_0", &self.eval_0);
    //transcript.append_scalar(b"eval_1", &self.eval_1);
    transcript.append_scalar(b"eval_2", &self.eval_2);
    transcript.append_scalar(b"eval_3", &self.eval_3);
    transcript.append_message(label, b"CubicPoly_end");
  }
}

/*#[test]
fn test_cubic_poly_interpolation() {
  let mut csprng: rand::rngs::OsRng = OsRng;

  // generate a random polynomial in point-value form
  let poly = CubicPoly::new(
    Scalar::random(&mut csprng),
    //Scalar::random(&mut csprng),
    Scalar::random(&mut csprng),
    Scalar::random(&mut csprng),
  );

  assert_eq!(poly.evaluate(&Scalar::zero()), poly.eval_at_zero());
  assert_eq!(poly.evaluate(&Scalar::one()), poly.eval_at_one());
  assert_eq!(poly.evaluate(&(2 as usize).to_scalar()), poly.eval_2);
  assert_eq!(poly.evaluate(&(3 as usize).to_scalar()), poly.eval_3);
}*/
