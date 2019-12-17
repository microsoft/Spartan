use super::scalar::{Scalar, ScalarBytesFromScalar};
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_COMPRESSED;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use digest::{ExtendableOutput, Input, XofReader};
use sha3::Shake256;

#[derive(Debug)]
pub struct MultiCommitGens {
  pub n: usize,
  pub G: Vec<RistrettoPoint>,
  pub h: RistrettoPoint,
}

#[allow(dead_code)]
impl MultiCommitGens {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let mut shake = Shake256::default();
    shake.input(RISTRETTO_BASEPOINT_COMPRESSED.as_bytes());
    shake.input(label);

    let mut reader = shake.xof_result();
    let mut gens: Vec<RistrettoPoint> = Vec::new();
    let mut uniform_bytes = [0u8; 64];
    for _ in 0..n + 1 {
      reader.read(&mut uniform_bytes);
      gens.push(RistrettoPoint::from_uniform_bytes(&uniform_bytes));
    }

    MultiCommitGens {
      n,
      G: gens[0..n].to_vec(),
      h: gens[n],
    }
  }
}

pub trait Commitments {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> RistrettoPoint;
}

impl Commitments for Scalar {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> RistrettoPoint {
    assert!(gens_n.n == 1);
    RistrettoPoint::vartime_multiscalar_mul(
      &[
        Scalar::decompress_scalar(&self),
        Scalar::decompress_scalar(&blind),
      ],
      &[gens_n.G[0], gens_n.h],
    )
  }
}

impl Commitments for Vec<Scalar> {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> RistrettoPoint {
    assert!(gens_n.n == self.len());
    RistrettoPoint::vartime_multiscalar_mul(&Scalar::decompress_vec(&self), &gens_n.G)
      + Scalar::decompress_scalar(&blind) * gens_n.h
  }
}

impl Commitments for [Scalar] {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> RistrettoPoint {
    assert_eq!(gens_n.n, self.len());
    RistrettoPoint::vartime_multiscalar_mul(&Scalar::decompress_seq(&self), &gens_n.G)
      + Scalar::decompress_scalar(&blind) * gens_n.h
  }
}

impl Commitments for Vec<bool> {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> RistrettoPoint {
    assert!(gens_n.n == self.len());
    let mut comm = Scalar::decompress_scalar(&blind) * gens_n.h;
    for i in 0..self.len() {
      if self[i] {
        comm = comm + gens_n.G[i];
      }
    }
    comm
  }
}

impl Commitments for [bool] {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> RistrettoPoint {
    assert!(gens_n.n == self.len());
    let mut comm = Scalar::decompress_scalar(&blind) * gens_n.h;
    for i in 0..self.len() {
      if self[i] {
        comm = comm + gens_n.G[i];
      }
    }
    comm
  }
}
