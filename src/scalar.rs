pub type Scalar = super::scalar_25519::Scalar;
pub type ScalarBytes = curve25519_dalek::scalar::Scalar;

pub trait ScalarFromPrimitives {
  fn to_scalar(self) -> Scalar;
}

impl ScalarFromPrimitives for usize {
  #[inline]
  fn to_scalar(self) -> Scalar {
    (0..self)
      .collect::<Vec<usize>>()
      .iter()
      .map(|&_i| Scalar::one())
      .sum()
  }
}

impl ScalarFromPrimitives for bool {
  #[inline]
  fn to_scalar(self) -> Scalar {
    if self {
      Scalar::one()
    } else {
      Scalar::zero()
    }
  }
}

pub trait ScalarBytesFromScalar {
  fn decompress_scalar(s: &Scalar) -> ScalarBytes;
  fn decompress_vec(v: &Vec<Scalar>) -> Vec<ScalarBytes>;
  fn decompress_seq(s: &[Scalar]) -> Vec<ScalarBytes>;
}

impl ScalarBytesFromScalar for Scalar {
  fn decompress_scalar(s: &Scalar) -> ScalarBytes {
    ScalarBytes::from_bytes_mod_order(s.to_bytes())
  }

  fn decompress_vec(v: &Vec<Scalar>) -> Vec<ScalarBytes> {
    (0..v.len())
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| Scalar::decompress_scalar(&v[i]))
      .collect::<Vec<ScalarBytes>>()
  }

  fn decompress_seq(s: &[Scalar]) -> Vec<ScalarBytes> {
    (0..s.len())
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| Scalar::decompress_scalar(&s[i]))
      .collect::<Vec<ScalarBytes>>()
  }
}
