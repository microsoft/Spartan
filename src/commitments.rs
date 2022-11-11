use super::group::{GroupElement, GroupElementAffine, VartimeMultiscalarMul, GROUP_BASEPOINT};
use super::scalar::Scalar;
use crate::group::CompressGroupElement;
use crate::parameters::*;
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::PrimeField;

use ark_sponge::poseidon::PoseidonSponge;
use ark_sponge::CryptographicSponge;

#[derive(Debug, Clone)]
pub struct MultiCommitGens {
  pub n: usize,
  pub G: Vec<GroupElement>,
  pub h: GroupElement,
}

impl MultiCommitGens {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let params = poseidon_params();
    let mut sponge = PoseidonSponge::new(&params);
    sponge.absorb(&label);
    sponge.absorb(&GROUP_BASEPOINT.compress().0);

    let mut gens: Vec<GroupElement> = Vec::new();
    for _ in 0..n + 1 {
      let mut el_aff: Option<GroupElementAffine> = None;
      while el_aff.is_none() {
        let uniform_bytes = sponge.squeeze_bytes(64);
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
