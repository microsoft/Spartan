use lazy_static::lazy_static;
use super::scalar::{Scalar};
use core::borrow::Borrow;
use core::ops::{Mul, MulAssign};
use ark_ec::{ProjectiveCurve, AffineCurve};

pub use ark_bls12_377::G1Projective as GroupElement;
pub use ark_bls12_377::G1Affine as AffineGroupElement;



// pub type CompressedGroup = curve25519_dalek::ristretto::CompressedRistretto;

// pub trait CompressedGroupExt {
//   type Group;
//   fn unpack(&self) -> Result<Self::Group, ProofVerifyError>;
// }


// what I should prolly do is implement compression and decompression operation on the GroupAffine

// impl CompressedGroupExt for CompressedGroup {
//   type Group = curve25519_dalek::ristretto::RistrettoPoint;
//   fn unpack(&self) -> Result<Self::Group, ProofVerifyError> {
//     self
//       .decompress()
//       .ok_or_else(|| ProofVerifyError::DecompressionError(self.to_bytes()))
//   }
// }

// ????
lazy_static! {
  pub static ref GROUP_BASEPOINT: GroupElement = GroupElement::prime_subgroup_generator();
}


// impl<'b> MulAssign<&'b Scalar> for GroupElement {
//   fn mul_assign(&mut self, scalar: &'b Scalar) {
//     let result = (self as &GroupElement).mul( scalar.into_repr());
//     *self = result;
//   }
// }

// // This game happens because dalek works with scalars as bytes representation but we want people to have an easy life and not care about this
// impl<'a, 'b> Mul<&'b Scalar> for &'a GroupElement {
//   type Output = GroupElement;
//   fn mul(self, scalar: &'b Scalar) -> GroupElement {
//     self * Scalar::into_repr(scalar)
//   }
// }

// impl<'a, 'b> Mul<&'b GroupElement> for &'a Scalar {
//   type Output = GroupElement;

//   fn mul(self, point: &'b GroupElement) -> GroupElement {
//     Scalar::into_repr(self) * point
//   }
// }

// macro_rules! define_mul_variants {
//   (LHS = $lhs:ty, RHS = $rhs:ty, Output = $out:ty) => {
//     impl<'b> Mul<&'b $rhs> for $lhs {
//       type Output = $out;
//       fn mul(self, rhs: &'b $rhs) -> $out {
//         &self * rhs
//       }
//     }

//     impl<'a> Mul<$rhs> for &'a $lhs {
//       type Output = $out;
//       fn mul(self, rhs: $rhs) -> $out {
//         self * &rhs
//       }
//     }

//     impl Mul<$rhs> for $lhs {
//       type Output = $out;
//       fn mul(self, rhs: $rhs) -> $out {
//         &self * &rhs
//       }
//     }
//   };
// }

// macro_rules! define_mul_assign_variants {
//   (LHS = $lhs:ty, RHS = $rhs:ty) => {
//     impl MulAssign<$rhs> for $lhs {
//       fn mul_assign(&mut self, rhs: $rhs) {
//         *self *= &rhs;
//       }
//     }
//   };
// }

// define_mul_assign_variants!(LHS = GroupElement, RHS = Scalar);
// define_mul_variants!(LHS = GroupElement, RHS = Scalar, Output = GroupElement);
// define_mul_variants!(LHS = Scalar, RHS = GroupElement, Output = GroupElement);


// TODO
// pub trait VartimeMultiscalarMul {
//   type Scalar;
//   fn vartime_multiscalar_mul<I, J>(scalars: I, points: J) -> Self
//   where
//     I: IntoIterator,
//     I::Item: Borrow<Self::Scalar>,
//     J: IntoIterator,
//     J::Item: Borrow<Self>,
//     Self: Clone;
// }

// impl VartimeMultiscalarMul for GroupElement {
//   type Scalar = super::scalar::Scalar;
//   fn vartime_multiscalar_mul<I, J>(scalars: I, points: J) -> Self
//   where
//     I: IntoIterator,
//     I::Item: Borrow<Self::Scalar>,
//     J: IntoIterator,
//     J::Item: Borrow<Self>,
//     Self: Clone,
//   {
//     // use curve25519_dalek::traits::VartimeMultiscalarMul;
//     <Self as VartimeMultiscalarMul>::vartime_multiscalar_mul(
//       scalars
//         .into_iter()
//         .map(|s| Scalar::into_repr(s.borrow()))
//         .collect::<Vec<Scalar>>(),
//       points,
//     )
//   }
// }
