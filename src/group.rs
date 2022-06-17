use ark_ec::{
  msm::VariableBaseMSM,
};
use ark_ff::{PrimeField};
use digest::DynDigest;
use lazy_static::lazy_static;
use num_bigint::BigInt;
use crate::errors::ProofVerifyError;

use lazy_static::lazy_static;
use num_bigint::BigInt;

use super::scalar::Scalar;
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_serialize::*;
use core::borrow::Borrow;
use core::ops::{Mul, MulAssign};
use ark_ec::{ProjectiveCurve, AffineCurve};
use ark_serialize::*;

pub type GroupElement = ark_bls12_377::G1Projective;
pub type GroupElementAffine = ark_bls12_377::G1Affine;
pub type CurveField = ark_bls12_377::Fq;

#[derive(Clone, Eq, PartialEq, Hash, Debug,  CanonicalSerialize, CanonicalDeserialize)]
pub struct CompressedGroup(pub Vec<u8>);

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
    let mut point_encoding = Vec::new();
    self.serialize(&mut point_encoding).unwrap();
    // println!("in compress {:?}", point_encoding);;
    CompressedGroup(point_encoding)
  }
}

impl DecompressGroupElement for GroupElement {
  fn decompress(encoded: &CompressedGroup) -> Option<Self>
  { 

      let res = GroupElement::deserialize(&*encoded.0);
      if res.is_err() {
         println!("{:?}", res);
        None
      } else {
        Some(res.unwrap())
      }
  }
} 

impl UnpackGroupElement for CompressedGroup {
  fn unpack(&self) -> Result<GroupElement, ProofVerifyError> {
    let encoded = self.0.clone();
      GroupElement::decompress(self).ok_or_else(|| ProofVerifyError::DecompressionError(encoded))
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

