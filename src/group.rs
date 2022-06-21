use ark_bls12_377::FrParameters;
use ark_ec::group::Group;
use ark_ec::{
  msm::VariableBaseMSM,
};
use ark_ff::{PrimeField, Fp256};
use digest::DynDigest;
use lazy_static::lazy_static;
use num_bigint::BigInt;
use crate::errors::ProofVerifyError;

use super::scalar::{Scalar};
use core::borrow::Borrow;
use core::ops::{Mul, MulAssign};
use ark_ec::{ProjectiveCurve, AffineCurve};
use ark_serialize::*;

pub type GroupElement = ark_bls12_377::G1Projective;
pub type GroupElementAffine = ark_bls12_377::G1Affine;

#[derive(Clone, Eq, Copy, PartialEq, Hash, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CompressedGroup(pub [u8; 48]);

lazy_static! {
  pub static ref GROUP_BASEPOINT: GroupElement = GroupElement::prime_subgroup_generator();
}

pub trait CompressGroupElement {
  fn compress(&self) -> CompressedGroup;
}

pub trait DecompressGroupElement {
  fn decompress(encoded: &CompressedGroup) -> Option<GroupElement>;
}

pub trait UnpackGroupElement {
  fn unpack(&self) -> Result<GroupElement, ProofVerifyError>;
}

impl CompressGroupElement for GroupElement {
  fn compress(&self) -> CompressedGroup {
    let mut point_encoding = [0u8; 48];
    self.serialize(&mut point_encoding[..]);
    CompressedGroup(point_encoding)
  }
}

impl DecompressGroupElement for GroupElement {
  fn decompress(encoded: &CompressedGroup) -> Option<Self>
  {
      let mut encoded_bytes = encoded.0;
      // TODO: make this cleaner
      let res = GroupElement::deserialize(&encoded_bytes[..]);
      if res.is_err() {
        None
      } else {
        Some(res.unwrap())
      }
  }
} 

impl UnpackGroupElement for CompressedGroup {
  fn unpack(&self) -> Result<GroupElement, ProofVerifyError> {
      GroupElement::decompress(&self).ok_or_else(|| ProofVerifyError::DecompressionError(self.0))
  }
}

pub trait VartimeMultiscalarMul {
  fn vartime_multiscalar_mul(scalars: &[Scalar], points: &[GroupElement]) -> GroupElement;
}

impl VartimeMultiscalarMul for GroupElement {
  fn  vartime_multiscalar_mul(
  scalars: &[Scalar],
  points: &[GroupElement],
) -> GroupElement{
  let repr_scalars= scalars.into_iter().map(|S| S.borrow().into_repr()).collect::<Vec<<Scalar as PrimeField>::BigInt>>();
  let aff_points = points.into_iter().map(|P| P.borrow().into_affine()).collect::<Vec<GroupElementAffine>>();
  VariableBaseMSM::multi_scalar_mul(aff_points.as_slice(), repr_scalars.as_slice())
}
}

