use crate::group::{CompressGroupElement, DecompressGroupElement};

use super::group::{GroupElement, VartimeMultiscalarMul, GROUP_BASEPOINT, GroupElementAffine};
use super::scalar::Scalar;
use ark_ff::PrimeField;
use digest::{ExtendableOutput, Input};
use sha3::Shake256;
use std::io::Read;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_ec::{ProjectiveCurve, AffineCurve};

#[derive(Debug)]
pub struct MultiCommitGens {
  pub n: usize,
  pub G: Vec<GroupElement>,
  pub h: GroupElement,
}

impl MultiCommitGens {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let mut shake = Shake256::default();
    shake.input(label);
    let mut generator_encoded = Vec::new();
    GROUP_BASEPOINT.serialize(&mut generator_encoded).unwrap();
    shake.input(generator_encoded);

    let mut reader = shake.xof_result();
    let mut gens: Vec<GroupElement> = Vec::new();
    let mut uniform_bytes = [0u8; 64];
    for _ in 0..n + 1 {
      let mut el_aff: Option<GroupElementAffine> = None;
      while el_aff.is_some() != true {
      reader.read_exact(&mut uniform_bytes).unwrap();
      el_aff = GroupElementAffine::from_random_bytes(&uniform_bytes);
    }
    let el = el_aff.unwrap().mul_by_cofactor_to_projective();
      gens.push(el);
    }

    MultiCommitGens {
      n,
      G: gens[..n].to_vec(),
      h: gens[n],
    }
  }

  pub fn clone(&self) -> MultiCommitGens {
    MultiCommitGens {
      n: self.n,
      h: self.h,
      G: self.G.clone(),
    }
  }

  pub fn split_at(&self, mid: usize) -> (MultiCommitGens, MultiCommitGens) {
    let (G1, G2) = self.G.split_at(mid);

    (
      MultiCommitGens {
        n: G1.len(),
        G: G1.to_vec(),
        h: self.h,
      },
      MultiCommitGens {
        n: G2.len(),
        G: G2.to_vec(),
        h: self.h,
      },
    )
  }
}

pub trait Commitments {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> GroupElement;
}

impl Commitments for Scalar {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> GroupElement {
    assert_eq!(gens_n.n, 1);
    GroupElement::vartime_multiscalar_mul(&[*self, *blind], &[gens_n.G[0], gens_n.h])
  }
}

impl Commitments for Vec<Scalar> {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> GroupElement {
    assert_eq!(gens_n.n, self.len());
    GroupElement::vartime_multiscalar_mul(self, &gens_n.G) + gens_n.h.mul(blind.into_repr())
  
  }
}

impl Commitments for [Scalar] {
  fn commit(&self, blind: &Scalar, gens_n: &MultiCommitGens) -> GroupElement {
    assert_eq!(gens_n.n, self.len());
    GroupElement::vartime_multiscalar_mul(self, &gens_n.G) + gens_n.h.mul(blind.into_repr())
    
  }
}
