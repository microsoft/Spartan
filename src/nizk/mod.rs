#![allow(clippy::too_many_arguments)]
use super::commitments::{Commitments, MultiCommitGens};
use super::errors::ProofVerifyError;
use super::group::{
  CompressedGroup, CompressGroupElement, UnpackGroupElement, GroupElement, DecompressGroupElement, GroupElementAffine};
use super::random::RandomTape;
use super::scalar::Scalar;
use super::transcript::{AppendToTranscript, ProofTranscript};
use ark_ec::group::Group;
use merlin::Transcript;
use ark_serialize::*;
use ark_ec::ProjectiveCurve;
use ark_ff::PrimeField;

mod bullet;
use bullet::BulletReductionProof;

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub struct KnowledgeProof {
  alpha: CompressedGroup,
  z1: Scalar,
  z2: Scalar,
}

impl KnowledgeProof {
  fn protocol_name() -> &'static [u8] {
    b"knowledge proof"
  }

  pub fn prove(
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x: &Scalar,
    r: &Scalar,
  ) -> (KnowledgeProof, CompressedGroup) {
    transcript.append_protocol_name(KnowledgeProof::protocol_name());

    // produce two random Scalars
    let t1 = random_tape.random_scalar(b"t1");
    let t2 = random_tape.random_scalar(b"t2");

    let C = x.commit(r, gens_n).compress();
    C.append_to_transcript(b"C", transcript);

    let alpha = t1.commit(&t2, gens_n).compress();
    alpha.append_to_transcript(b"alpha", transcript);

    let c = transcript.challenge_scalar(b"c");

    let z1 = c * x + t1;
    let z2 =  c * r + t2;

    (KnowledgeProof { alpha, z1, z2 }, C)
  }

  pub fn verify(
    &self,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    C: &
    CompressedGroup,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(KnowledgeProof::protocol_name());
    C.append_to_transcript(b"C", transcript);
    self.alpha.append_to_transcript(b"alpha", transcript);

    let c = transcript.challenge_scalar(b"c");

    let lhs = self.z1.commit(&self.z2, gens_n).compress();
    let rhs = ( C.unpack()?.mul(c.into_repr()) + self.alpha.unpack()?).compress();

    if lhs == rhs {
      Ok(())
    } else {
      Err(ProofVerifyError::InternalError)
    }
  }
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub struct EqualityProof {
  alpha: 
  CompressedGroup,
  z: Scalar,
}

impl EqualityProof {
  fn protocol_name() -> &'static [u8] {
    b"equality proof"
  }

  pub fn prove(
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    v1: &Scalar,
    s1: &Scalar,
    v2: &Scalar,
    s2: &Scalar,
  ) -> (EqualityProof, 
    CompressedGroup, 
  CompressedGroup) {
    transcript.append_protocol_name(EqualityProof::protocol_name());

    // produce a random Scalar
    let r = random_tape.random_scalar(b"r");

    let C1 = v1.commit(s1, gens_n).compress();
    C1.append_to_transcript(b"C1", transcript);

    let C2 = v2.commit(s2, gens_n).compress();
    C2.append_to_transcript(b"C2", transcript);

    let alpha = gens_n.h.mul(r.into_repr()).compress();
    alpha.append_to_transcript(b"alpha", transcript);

    let c = transcript.challenge_scalar(b"c");

    let z = c * ((*s1) - s2) + r;

    (EqualityProof { alpha, z }, C1, C2)
  }

  pub fn verify(
    &self,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    C1: &
    CompressedGroup,
    C2: &
    CompressedGroup,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(EqualityProof::protocol_name());
    C1.append_to_transcript(b"C1", transcript);
    C2.append_to_transcript(b"C2", transcript);
    self.alpha.append_to_transcript(b"alpha", transcript);

    let c = transcript.challenge_scalar(b"c");
    let rhs = {
      let C = C1.unpack()? - C2.unpack()?;
      (C.mul(c.into_repr()) + self.alpha.unpack()?).compress()
    };
    println!("rhs {:?}", rhs);

    let lhs = gens_n.h.mul(self.z.into_repr()).compress();
    println!("lhs {:?}", lhs);
    if lhs == rhs {
      Ok(())
    } else {
      Err(ProofVerifyError::InternalError)
    }
  }
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub struct ProductProof {
  alpha: 
  CompressedGroup,
  beta: 
  CompressedGroup,
  delta: 
  CompressedGroup,
  z: Vec<Scalar>,
}

impl ProductProof {
  fn protocol_name() -> &'static [u8] {
    b"product proof"
  }

  pub fn prove(
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x: &Scalar,
    rX: &Scalar,
    y: &Scalar,
    rY: &Scalar,
    z: &Scalar,
    rZ: &Scalar,
  ) -> (
    ProductProof,
    
    CompressedGroup,
    
    CompressedGroup,
    
    CompressedGroup,
  ) {
    transcript.append_protocol_name(ProductProof::protocol_name());

    // produce five random Scalar
    let b1 = random_tape.random_scalar(b"b1");
    let b2 = random_tape.random_scalar(b"b2");
    let b3 = random_tape.random_scalar(b"b3");
    let b4 = random_tape.random_scalar(b"b4");
    let b5 = random_tape.random_scalar(b"b5");

    let X_unc =  x.commit(rX, gens_n);
    
    
    let X = X_unc.compress();
    X.append_to_transcript(b"X", transcript);

    let X_new = GroupElement::decompress(&X);

    assert_eq!(X_unc, X_new.unwrap());
   

    let Y = y.commit(rY, gens_n).compress();
    Y.append_to_transcript(b"Y", transcript);

    let Z = z.commit(rZ, gens_n).compress();
    Z.append_to_transcript(b"Z", transcript);

    let alpha = b1.commit(&b2, gens_n).compress();
    alpha.append_to_transcript(b"alpha", transcript);

    let beta = b3.commit(&b4, gens_n).compress();
    beta.append_to_transcript(b"beta", transcript);

    let delta = {
      let gens_X = &MultiCommitGens {
        n: 1,
        G: vec![GroupElement::decompress(&X).unwrap()],
        h: gens_n.h,
      };
      b3.commit(&b5, gens_X).compress()
    };
    delta.append_to_transcript(b"delta", transcript);

    let c = transcript.challenge_scalar(b"c");

    let z1 = b1 + c * x;
    let z2 = b2 + c * rX;
    let z3 = b3 + c * y;
    let z4 = b4 + c * rY;
    let z5 = b5 + c * ((*rZ) - (*rX) * y);
    let z = [z1, z2, z3, z4, z5].to_vec();

    (
      ProductProof {
        alpha,
        beta,
        delta,
        z,
      },
      X,
      Y,
      Z,
    )
  }

  fn check_equality(
    P: &
    CompressedGroup,
    X: &
    CompressedGroup,
    c: &Scalar,
    gens_n: &MultiCommitGens,
    z1: &Scalar,
    z2: &Scalar,
  ) -> bool {
    println!("{:?}", X);
    let lhs = (GroupElement::decompress(P).unwrap() + GroupElement::decompress(X).unwrap().mul(c.into_repr())).compress();
    let rhs = z1.commit(z2, gens_n).compress();

    lhs == rhs
  }

  pub fn verify(
    &self,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    X: &
    CompressedGroup,
    Y: &
    CompressedGroup,
    Z: &
    CompressedGroup,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(ProductProof::protocol_name());

    X.append_to_transcript(b"X", transcript);
    Y.append_to_transcript(b"Y", transcript);
    Z.append_to_transcript(b"Z", transcript);
    self.alpha.append_to_transcript(b"alpha", transcript);
    self.beta.append_to_transcript(b"beta", transcript);
    self.delta.append_to_transcript(b"delta", transcript);

    let z1 = self.z[0];
    let z2 = self.z[1];
    let z3 = self.z[2];
    let z4 = self.z[3];
    let z5 = self.z[4];

    let c = transcript.challenge_scalar(b"c");

    if ProductProof::check_equality(&self.alpha, X, &c, gens_n, &z1, &z2)
      && ProductProof::check_equality(&self.beta, Y, &c, gens_n, &z3, &z4)
      && ProductProof::check_equality(
        &self.delta,
        Z,
        &c,
        &MultiCommitGens {
          n: 1,
          G: vec![X.unpack()?],
          h: gens_n.h,
        },
        &z3,
        &z5,
      )
    {
      Ok(())
    } else {
      Err(ProofVerifyError::InternalError)
    }
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DotProductProof {
  delta: 
  CompressedGroup,
  beta: 
  CompressedGroup,
  z: Vec<Scalar>,
  z_delta: Scalar,
  z_beta: Scalar,
}

impl DotProductProof {
  fn protocol_name() -> &'static [u8] {
    b"dot product proof"
  }

  pub fn compute_dotproduct(a: &[Scalar], b: &[Scalar]) -> Scalar {
    assert_eq!(a.len(), b.len());
    (0..a.len()).map(|i| a[i] * b[i]).sum()
  }

  pub fn prove(
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_vec: &[Scalar],
    blind_x: &Scalar,
    a_vec: &[Scalar],
    y: &Scalar,
    blind_y: &Scalar,
  ) -> (DotProductProof, 
    CompressedGroup, 
  CompressedGroup) {
    transcript.append_protocol_name(DotProductProof::protocol_name());

    let n = x_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());
    assert_eq!(gens_n.n, a_vec.len());
    assert_eq!(gens_1.n, 1);

    // produce randomness for the proofs
    let d_vec = random_tape.random_vector(b"d_vec", n);
    let r_delta = random_tape.random_scalar(b"r_delta");
    let r_beta = random_tape.random_scalar(b"r_beta");

    let Cx = x_vec.commit(blind_x, gens_n).compress();
    Cx.append_to_transcript(b"Cx", transcript);

    let Cy = y.commit(blind_y, gens_1).compress();
    Cy.append_to_transcript(b"Cy", transcript);

    a_vec.append_to_transcript(b"a", transcript);

    let delta = d_vec.commit(&r_delta, gens_n).compress();
    delta.append_to_transcript(b"delta", transcript);

    let dotproduct_a_d = DotProductProof::compute_dotproduct(a_vec, &d_vec);

    let beta = dotproduct_a_d.commit(&r_beta, gens_1).compress();
    beta.append_to_transcript(b"beta", transcript);

    let c = transcript.challenge_scalar(b"c");

    let z = (0..d_vec.len())
      .map(|i| c * x_vec[i] + d_vec[i])
      .collect::<Vec<Scalar>>();

    let z_delta = c * blind_x + r_delta;
    let z_beta = c * blind_y + r_beta;

    (
      DotProductProof {
        delta,
        beta,
        z,
        z_delta,
        z_beta,
      },
      Cx,
      Cy,
    )
  }

  pub fn verify(
    &self,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    a: &[Scalar],
    Cx: &
    CompressedGroup,
    Cy: &
    CompressedGroup,
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(gens_n.n, a.len());
    assert_eq!(gens_1.n, 1);

    transcript.append_protocol_name(DotProductProof::protocol_name());
    Cx.append_to_transcript(b"Cx", transcript);
    Cy.append_to_transcript(b"Cy", transcript);
    a.append_to_transcript(b"a", transcript);
    self.delta.append_to_transcript(b"delta", transcript);
    self.beta.append_to_transcript(b"beta", transcript);

    let c = transcript.challenge_scalar(b"c");

    let mut result =
    Cx.unpack()?.mul(c.into_repr()) + self.delta.unpack()? == self.z.commit(&self.z_delta, gens_n);

    let dotproduct_z_a = DotProductProof::compute_dotproduct(&self.z, a);
    result &= Cy.unpack()?.mul(c.into_repr()) + self.beta.unpack()? == dotproduct_z_a.commit(&self.z_beta, gens_1);
    if result {
      Ok(())
    } else {
      Err(ProofVerifyError::InternalError)
    }
  }
}

pub struct DotProductProofGens {
  n: usize,
  pub gens_n: MultiCommitGens,
  pub gens_1: MultiCommitGens,
}

impl DotProductProofGens {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let (gens_n, gens_1) = MultiCommitGens::new(n + 1, label).split_at(n);
    DotProductProofGens { n, gens_n, gens_1 }
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DotProductProofLog {
  bullet_reduction_proof: BulletReductionProof,
  delta: 
  CompressedGroup,
  beta: 
  CompressedGroup,
  z1: Scalar,
  z2: Scalar,
}

impl DotProductProofLog {
  fn protocol_name() -> &'static [u8] {
    b"dot product proof (log)"
  }

  pub fn compute_dotproduct(a: &[Scalar], b: &[Scalar]) -> Scalar {
    assert_eq!(a.len(), b.len());
    (0..a.len()).map(|i| a[i] * b[i]).sum()
  }

  pub fn prove(
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_vec: &[Scalar],
    blind_x: &Scalar,
    a_vec: &[Scalar],
    y: &Scalar,
    blind_y: &Scalar,
  ) -> (DotProductProofLog, 
    CompressedGroup, 
  CompressedGroup) {
    transcript.append_protocol_name(DotProductProofLog::protocol_name());

    let n = x_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());
    assert_eq!(gens.n, n);

    // produce randomness for generating a proof
    let d = random_tape.random_scalar(b"d");
    let r_delta = random_tape.random_scalar(b"r_delta");
    let r_beta = random_tape.random_scalar(b"r_delta");
    let blinds_vec = {
      let v1 = random_tape.random_vector(b"blinds_vec_1", 2 * n.log2() as usize);
      let v2 = random_tape.random_vector(b"blinds_vec_2", 2 * n.log2() as usize);
      (0..v1.len())
        .map(|i| (v1[i], v2[i]))
        .collect::<Vec<(Scalar, Scalar)>>()
    };

    let Cx = x_vec.commit(blind_x, &gens.gens_n).compress();
    Cx.append_to_transcript(b"Cx", transcript);

    let Cy = y.commit(blind_y, &gens.gens_1).compress();
    Cy.append_to_transcript(b"Cy", transcript);

    a_vec.append_to_transcript(b"a", transcript);

    let blind_Gamma = (*blind_x) + blind_y;
    let (bullet_reduction_proof, _Gamma_hat, x_hat, a_hat, g_hat, rhat_Gamma) =
      BulletReductionProof::prove(
        transcript,
        &gens.gens_1.G[0],
        &gens.gens_n.G,
        &gens.gens_n.h,
        x_vec,
        a_vec,
        &blind_Gamma,
        &blinds_vec,
      );
    let y_hat = x_hat * a_hat;

    let delta = {
      let gens_hat = MultiCommitGens {
        n: 1,
        G: vec![g_hat],
        h: gens.gens_1.h,
      };
      d.commit(&r_delta, &gens_hat).compress()
    };
    delta.append_to_transcript(b"delta", transcript);

    let beta = d.commit(&r_beta, &gens.gens_1).compress();
    beta.append_to_transcript(b"beta", transcript);

    let c = transcript.challenge_scalar(b"c");

    let z1 = d + c * y_hat;
    let z2 = a_hat * (c * rhat_Gamma + r_beta) + r_delta;

    (
      DotProductProofLog {
        bullet_reduction_proof,
        delta,
        beta,
        z1,
        z2,
      },
      Cx,
      Cy,
    )
  }

  pub fn verify(
    &self,
    n: usize,
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    a: &[Scalar],
    Cx: &
    CompressedGroup,
    Cy: &
    CompressedGroup,
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(gens.n, n);
    assert_eq!(a.len(), n);

    transcript.append_protocol_name(DotProductProofLog::protocol_name());
    Cx.append_to_transcript(b"Cx", transcript);
    Cy.append_to_transcript(b"Cy", transcript);
    a.append_to_transcript(b"a", transcript);

    let Gamma = Cx.unpack()? + Cy.unpack()?;

    let (g_hat, Gamma_hat, a_hat) =
      self
        .bullet_reduction_proof
        .verify(n, a, transcript, &Gamma, &gens.gens_n.G)?;
    self.delta.append_to_transcript(b"delta", transcript);
    self.beta.append_to_transcript(b"beta", transcript);

    let c = transcript.challenge_scalar(b"c");

    let c_s = &c;
    let beta_s = self.beta.unpack()?;
    let a_hat_s = &a_hat;
    let delta_s = self.delta.unpack()?;
    let z1_s = &self.z1;
    let z2_s = &self.z2;

    let lhs = ((Gamma_hat.mul(c_s.into_repr()) + beta_s).mul(a_hat_s.into_repr()) + delta_s).compress();
    let rhs = ((g_hat + gens.gens_1.G[0].mul(a_hat_s.into_repr())).mul(z1_s.into_repr()) + gens.gens_1.h.mul(z2_s.into_repr())).compress();

    assert_eq!(lhs, rhs);

    if lhs == rhs {
      Ok(())
    } else {
      Err(ProofVerifyError::InternalError)
    }
  }
}

#[cfg(test)]
mod tests {
  use std::marker::PhantomData;

use crate::group::VartimeMultiscalarMul;

use super::*;
use ark_bls12_377::{G1Affine, Fq, FqParameters};
use ark_ff::{Fp384, BigInteger384};
use ark_std::{UniformRand};
  #[test]
  fn check_knowledgeproof() {
  let mut rng = ark_std::rand::thread_rng();

    let gens_1 = MultiCommitGens::new(1, b"test-knowledgeproof");

    let x = Scalar::rand(&mut rng);
    let r = Scalar::rand(&mut rng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, committed_value) =
      KnowledgeProof::prove(&gens_1, &mut prover_transcript, &mut random_tape, &x, &r);

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &mut verifier_transcript, &committed_value)
      .is_ok());
  }

  #[test]
  fn check_equalityproof() {
  let mut rng = ark_std::rand::thread_rng();

    let gens_1 = MultiCommitGens::new(1, b"test-equalityproof");
    let v1 = Scalar::rand(&mut rng);
    let v2 = v1;
    let s1 = Scalar::rand(&mut rng);
    let s2 = Scalar::rand(&mut rng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, C1, C2) = EqualityProof::prove(
      &gens_1,
      &mut prover_transcript,
      &mut random_tape,
      &v1,
      &s1,
      &v2,
      &s2,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &mut verifier_transcript, &C1, &C2)
      .is_ok());
  }
  
  #[test]
  fn check_productproof() {
  let mut rng = ark_std::rand::thread_rng();
  let pt = GroupElement::rand(&mut rng);
  let pt_c = pt.compress();
  let pt2 = GroupElement::decompress(&pt_c).unwrap();
  assert_eq!(pt, pt2);

    let gens_1 = MultiCommitGens::new(1, b"test-productproof");
    let x = Scalar::rand(&mut rng);
    let rX = Scalar::rand(&mut rng);
    let y = Scalar::rand(&mut rng);
    let rY = Scalar::rand(&mut rng);
    let z = x * y;
    let rZ = Scalar::rand(&mut rng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, X, Y, Z) = ProductProof::prove(
      &gens_1,
      &mut prover_transcript,
      &mut random_tape,
      &x,
      &rX,
      &y,
      &rY,
      &z,
      &rZ,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &mut verifier_transcript, &X, &Y, &Z)
      .is_ok());
  }

  #[test]
  fn check_dotproductproof() {
  let mut rng = ark_std::rand::thread_rng();

    let n = 1024;

    let gens_1 = MultiCommitGens::new(1, b"test-two");
    let gens_1024 = MultiCommitGens::new(n, b"test-1024");

    let mut x: Vec<Scalar> = Vec::new();
    let mut a: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      x.push(Scalar::rand(&mut rng));
      a.push(Scalar::rand(&mut rng));
    }
    let y = DotProductProofLog::compute_dotproduct(&x, &a);
    let r_x = Scalar::rand(&mut rng);
    let r_y = Scalar::rand(&mut rng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, Cx, Cy) = DotProductProof::prove(
      &gens_1,
      &gens_1024,
      &mut prover_transcript,
      &mut random_tape,
      &x,
      &r_x,
      &a,
      &y,
      &r_y,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &gens_1024, &mut verifier_transcript, &a, &Cx, &Cy)
      .is_ok());
  }

  #[test]
  fn check_dotproductproof_log() {
  let mut rng = ark_std::rand::thread_rng();

    let n = 1024;

    let gens = DotProductProofGens::new(n, b"test-1024");

    let x: Vec<Scalar> = (0..n).map(|_i| Scalar::rand(&mut rng)).collect();
    let a: Vec<Scalar> = (0..n).map(|_i| Scalar::rand(&mut rng)).collect();
    let y = DotProductProof::compute_dotproduct(&x, &a);

    let r_x = Scalar::rand(&mut rng);
    let r_y = Scalar::rand(&mut rng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, Cx, Cy) = DotProductProofLog::prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &x,
      &r_x,
      &a,
      &y,
      &r_y,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(n, &gens, &mut verifier_transcript, &a, &Cx, &Cy)
      .is_ok());
  }
}
