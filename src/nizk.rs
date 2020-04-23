use super::bullet::BulletReductionProof;
use super::commitments::{Commitments, MultiCommitGens};
use super::errors::ProofVerifyError;
use super::math::Math;
use super::scalar::{Scalar, ScalarBytesFromScalar};
use super::transcript::ProofTranscript;
use curve25519_dalek::ristretto::CompressedRistretto;
use merlin::Transcript;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct KnowledgeProof {
  alpha: CompressedRistretto,
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
    x: &Scalar,
    r: &Scalar,
    t1: &Scalar,
    t2: &Scalar,
  ) -> (KnowledgeProof, CompressedRistretto) {
    transcript.append_protocol_name(KnowledgeProof::protocol_name());

    let C = x.commit(&r, gens_n).compress();

    transcript.append_point(b"C", &C);

    let alpha = t1.commit(&t2, gens_n).compress();
    transcript.append_point(b"alpha", &alpha);

    let c = transcript.challenge_scalar(b"c");

    let z1 = x * c + t1;
    let z2 = r * c + t2;

    (KnowledgeProof { alpha, z1, z2 }, C)
  }

  pub fn verify(
    &self,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    C: &CompressedRistretto,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(KnowledgeProof::protocol_name());
    transcript.append_point(b"C", &C);
    transcript.append_point(b"alpha", &self.alpha);

    let c = transcript.challenge_scalar(b"c");

    let lhs = self.z1.commit(&self.z2, gens_n).compress();
    let rhs = (Scalar::decompress_scalar(&c) * C.decompress().expect("Could not decompress C")
      + self
        .alpha
        .decompress()
        .expect("Could not decompress self.alpha"))
    .compress();

    if lhs == rhs {
      Ok(())
    } else {
      Err(ProofVerifyError)
    }
  }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct EqualityProof {
  alpha: CompressedRistretto,
  z: Scalar,
}

impl EqualityProof {
  fn protocol_name() -> &'static [u8] {
    b"equality proof"
  }

  pub fn prove(
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    v1: &Scalar,
    s1: &Scalar,
    v2: &Scalar,
    s2: &Scalar,
    r: &Scalar,
  ) -> (EqualityProof, CompressedRistretto, CompressedRistretto) {
    transcript.append_protocol_name(EqualityProof::protocol_name());

    let C1 = v1.commit(&s1, gens_n).compress();
    transcript.append_point(b"C1", &C1);

    let C2 = v2.commit(&s2, gens_n).compress();
    transcript.append_point(b"C2", &C2);

    let alpha = (Scalar::decompress_scalar(&r) * gens_n.h).compress();
    transcript.append_point(b"alpha", &alpha);

    let c = transcript.challenge_scalar(b"c");

    let z = c * (s1 - s2) + r;

    (EqualityProof { alpha, z }, C1, C2)
  }

  pub fn verify(
    &self,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    C1: &CompressedRistretto,
    C2: &CompressedRistretto,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(EqualityProof::protocol_name());
    transcript.append_point(b"C1", &C1);
    transcript.append_point(b"C2", &C2);
    transcript.append_point(b"alpha", &self.alpha);

    let c = transcript.challenge_scalar(b"c");

    let lhs = (Scalar::decompress_scalar(&self.z) * gens_n.h).compress();

    let C = C1.decompress().unwrap() - C2.decompress().unwrap();
    let rhs = (Scalar::decompress_scalar(&c) * C + self.alpha.decompress().unwrap()).compress();

    if lhs == rhs {
      Ok(())
    } else {
      Err(ProofVerifyError)
    }
  }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct ProductProof {
  alpha: CompressedRistretto,
  beta: CompressedRistretto,
  delta: CompressedRistretto,
  z: [Scalar; 5],
}

impl ProductProof {
  fn protocol_name() -> &'static [u8] {
    b"product proof"
  }

  pub fn prove(
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    x: &Scalar,
    rX: &Scalar,
    y: &Scalar,
    rY: &Scalar,
    z: &Scalar,
    rZ: &Scalar,
    b1: &Scalar,
    b2: &Scalar,
    b3: &Scalar,
    b4: &Scalar,
    b5: &Scalar,
  ) -> (
    ProductProof,
    CompressedRistretto,
    CompressedRistretto,
    CompressedRistretto,
  ) {
    transcript.append_protocol_name(ProductProof::protocol_name());

    let X = x.commit(&rX, gens_n).compress();
    transcript.append_point(b"X", &X);

    let Y = y.commit(&rY, gens_n).compress();
    transcript.append_point(b"Y", &Y);

    let Z = z.commit(&rZ, gens_n).compress();
    transcript.append_point(b"Z", &Z);

    let alpha = b1.commit(&b2, gens_n).compress();
    transcript.append_point(b"alpha", &alpha);

    let beta = b3.commit(&b4, gens_n).compress();
    transcript.append_point(b"beta", &beta);

    let gens_X = &MultiCommitGens {
      n: 1,
      G: vec![X.decompress().unwrap()],
      h: gens_n.h,
    };
    let delta = b3.commit(&b5, gens_X).compress();
    transcript.append_point(b"delta", &delta);

    let c = transcript.challenge_scalar(b"c");

    let z1 = b1 + c * x;
    let z2 = b2 + c * rX;
    let z3 = b3 + c * y;
    let z4 = b4 + c * rY;
    let z5 = b5 + c * (rZ - rX * y);
    let z = [z1, z2, z3, z4, z5];

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
    P: &CompressedRistretto,
    X: &CompressedRistretto,
    c: &Scalar,
    gens_n: &MultiCommitGens,
    z1: &Scalar,
    z2: &Scalar,
  ) -> bool {
    let lhs = (P.decompress().unwrap() + Scalar::decompress_scalar(&c) * X.decompress().unwrap())
      .compress();
    let rhs = z1.commit(&z2, gens_n).compress();

    if lhs == rhs {
      true
    } else {
      false
    }
  }

  pub fn verify(
    &self,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    X: &CompressedRistretto,
    Y: &CompressedRistretto,
    Z: &CompressedRistretto,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(ProductProof::protocol_name());

    transcript.append_point(b"X", &X);
    transcript.append_point(b"Y", &Y);
    transcript.append_point(b"Z", &Z);
    transcript.append_point(b"alpha", &self.alpha);
    transcript.append_point(b"beta", &self.beta);
    transcript.append_point(b"delta", &self.delta);

    let z1 = self.z[0];
    let z2 = self.z[1];
    let z3 = self.z[2];
    let z4 = self.z[3];
    let z5 = self.z[4];

    let c = transcript.challenge_scalar(b"c");

    if ProductProof::check_equality(&self.alpha, &X, &c, &gens_n, &z1, &z2)
      && ProductProof::check_equality(&self.beta, &Y, &c, &gens_n, &z3, &z4)
      && ProductProof::check_equality(
        &self.delta,
        &Z,
        &c,
        &MultiCommitGens {
          n: 1,
          G: vec![X.decompress().unwrap()],
          h: gens_n.h,
        },
        &z3,
        &z5,
      )
    {
      Ok(())
    } else {
      Err(ProofVerifyError)
    }
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DotProductProof {
  delta: CompressedRistretto,
  beta: CompressedRistretto,
  z: Vec<Scalar>,
  z_delta: Scalar,
  z_beta: Scalar,
}

#[allow(dead_code)]
impl DotProductProof {
  fn protocol_name() -> &'static [u8] {
    b"dot product proof"
  }

  pub fn compute_dotproduct(a: &Vec<Scalar>, b: &Vec<Scalar>) -> Scalar {
    assert_eq!(a.len(), b.len());
    (0..a.len()).map(|i| &a[i] * &b[i]).sum()
  }

  pub fn prove(
    n: usize,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    x: &Vec<Scalar>,
    r_x: &Scalar,
    a: &Vec<Scalar>,
    y: &Scalar,
    r_y: &Scalar,
    d: &Vec<Scalar>,
    r_delta: &Scalar,
    r_beta: &Scalar,
  ) -> (DotProductProof, CompressedRistretto, CompressedRistretto) {
    assert_eq!(x.len(), n);
    assert_eq!(d.len(), n);
    assert_eq!(x.len(), a.len());
    assert_eq!(gens_n.n, a.len());
    assert_eq!(gens_1.n, 1);

    transcript.append_protocol_name(DotProductProof::protocol_name());

    let Cx = x.commit(&r_x, gens_n).compress();
    transcript.append_point(b"Cx", &Cx);

    let Cy = y.commit(&r_y, gens_1).compress();
    transcript.append_point(b"Cy", &Cy);

    let delta = d.commit(&r_delta, gens_n).compress();
    transcript.append_point(b"delta", &delta);

    let dotproduct_a_d = DotProductProof::compute_dotproduct(&a, &d);

    let beta = dotproduct_a_d.commit(&r_beta, gens_1).compress();
    transcript.append_point(b"beta", &beta);

    let c = transcript.challenge_scalar(b"c");

    let z = (0..d.len())
      .map(|i| c * x[i] + d[i])
      .collect::<Vec<Scalar>>();

    let z_delta = c * r_x + r_delta;
    let z_beta = c * r_y + r_beta;

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
    a: &Vec<Scalar>,
    Cx: &CompressedRistretto,
    Cy: &CompressedRistretto,
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(gens_n.n, a.len());
    assert_eq!(gens_1.n, 1);

    transcript.append_protocol_name(DotProductProof::protocol_name());
    transcript.append_point(b"Cx", &Cx);
    transcript.append_point(b"Cy", &Cy);
    transcript.append_point(b"delta", &self.delta);
    transcript.append_point(b"beta", &self.beta);

    let c = transcript.challenge_scalar(b"c");

    let mut result = Scalar::decompress_scalar(&c) * Cx.decompress().unwrap()
      + self.delta.decompress().unwrap()
      == self.z.commit(&self.z_delta, gens_n);

    let dotproduct_z_a = DotProductProof::compute_dotproduct(&self.z, &a);
    result &= Scalar::decompress_scalar(&c) * Cy.decompress().unwrap()
      + self.beta.decompress().unwrap()
      == dotproduct_z_a.commit(&self.z_beta, gens_1);

    if result {
      Ok(())
    } else {
      Err(ProofVerifyError)
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
    let (gens_n, gens_1) = MultiCommitGens::new(n + 1, label).split_at_mut(n);
    DotProductProofGens { n, gens_n, gens_1 }
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DotProductProofLog {
  bullet_reduction_proof: BulletReductionProof,
  delta: CompressedRistretto,
  beta: CompressedRistretto,
  z1: Scalar,
  z2: Scalar,
}

#[allow(dead_code)]
impl DotProductProofLog {
  fn protocol_name() -> &'static [u8] {
    b"dot product proof (log)"
  }

  pub fn compute_dotproduct(a: &Vec<Scalar>, b: &Vec<Scalar>) -> Scalar {
    assert_eq!(a.len(), b.len());
    (0..a.len()).map(|i| &a[i] * &b[i]).sum()
  }

  pub fn prove(
    n: usize,
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    x: &Vec<Scalar>,
    r_x: &Scalar,
    a: &Vec<Scalar>,
    y: &Scalar,
    r_y: &Scalar,
    d: &Scalar,
    r_delta: &Scalar,
    r_beta: &Scalar,
    blinds_vec: &Vec<(Scalar, Scalar)>,
  ) -> (DotProductProofLog, CompressedRistretto, CompressedRistretto) {
    assert_eq!(x.len(), n);
    assert_eq!(x.len(), a.len());
    assert_eq!(blinds_vec.len(), 2 * n.log2());
    assert_eq!(gens.n, n);

    transcript.append_protocol_name(DotProductProofLog::protocol_name());

    let Cx = x.commit(&r_x, &gens.gens_n);
    let Cx_compressed = Cx.compress();
    transcript.append_point(b"Cx", &Cx_compressed);

    let Cy = y.commit(&r_y, &gens.gens_1);
    let Cy_compressed = Cy.compress();
    transcript.append_point(b"Cy", &Cy_compressed);

    // let Gamma = Cx + Cy;
    let r_Gamma = r_x + r_y;

    let (bullet_reduction_proof, _Gamma_hat, x_hat, a_hat, g_hat, rhat_Gamma) =
      BulletReductionProof::prove(
        transcript,
        &gens.gens_1.G[0],
        &gens.gens_n.G,
        &gens.gens_n.h,
        x,
        a,
        &r_Gamma,
        blinds_vec,
      );
    let y_hat = x_hat * a_hat;

    let gens_hat = MultiCommitGens {
      n: 1,
      G: vec![g_hat],
      h: gens.gens_1.h,
    };

    let delta = d.commit(r_delta, &gens_hat).compress();
    transcript.append_point(b"delta", &delta);

    let beta = d.commit(r_beta, &gens.gens_1).compress();
    transcript.append_point(b"beta", &beta);

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
      Cx_compressed,
      Cy_compressed,
    )
  }

  pub fn verify(
    &self,
    n: usize,
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    a: &Vec<Scalar>,
    Cx: &CompressedRistretto,
    Cy: &CompressedRistretto,
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(gens.n, n);
    assert_eq!(a.len(), n);

    transcript.append_protocol_name(DotProductProofLog::protocol_name());
    transcript.append_point(b"Cx", &Cx);
    transcript.append_point(b"Cy", &Cy);

    let Gamma = Cx.decompress().unwrap() + Cy.decompress().unwrap();

    let (g_hat, Gamma_hat, a_hat) = self
      .bullet_reduction_proof
      .verify(n, a, transcript, &Gamma, &gens.gens_n.G)
      .unwrap();

    transcript.append_point(b"delta", &self.delta);
    transcript.append_point(b"beta", &self.beta);

    let c = transcript.challenge_scalar(b"c");

    let c_s = Scalar::decompress_scalar(&c);
    let beta_s = self.beta.decompress().unwrap();
    let a_hat_s = Scalar::decompress_scalar(&a_hat);
    let delta_s = self.delta.decompress().unwrap();
    let z1_s = Scalar::decompress_scalar(&self.z1);
    let z2_s = Scalar::decompress_scalar(&self.z2);

    let lhs = ((Gamma_hat * c_s + beta_s) * a_hat_s + delta_s).compress();
    let rhs = ((g_hat + &gens.gens_1.G[0] * a_hat_s) * z1_s + gens.gens_1.h * z2_s).compress();

    assert_eq!(lhs, rhs);

    if lhs == rhs {
      Ok(())
    } else {
      Err(ProofVerifyError)
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;
  #[test]
  fn check_knowledgeproof() {
    let mut csprng: OsRng = OsRng;

    let gens_1 = MultiCommitGens::new(1, b"test-knowledgeproof");

    let x = Scalar::random(&mut csprng);
    let r = Scalar::random(&mut csprng);
    let t1 = Scalar::random(&mut csprng);
    let t2 = Scalar::random(&mut csprng);

    let mut prover_transcript = Transcript::new(b"example");
    let (proof, committed_value) =
      KnowledgeProof::prove(&gens_1, &mut prover_transcript, &x, &r, &t1, &t2);

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &mut verifier_transcript, &committed_value)
      .is_ok());
  }

  #[test]
  fn check_equalityproof() {
    let mut csprng: OsRng = OsRng;

    let gens_1 = MultiCommitGens::new(1, b"test-equalityproof");
    let v1 = Scalar::random(&mut csprng);
    let v2 = v1;
    let s1 = Scalar::random(&mut csprng);
    let s2 = Scalar::random(&mut csprng);
    let r = Scalar::random(&mut csprng);

    let mut prover_transcript = Transcript::new(b"example");
    let (proof, C1, C2) =
      EqualityProof::prove(&gens_1, &mut prover_transcript, &v1, &s1, &v2, &s2, &r);

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &mut verifier_transcript, &C1, &C2)
      .is_ok());
  }

  #[test]
  fn check_productproof() {
    let mut csprng: OsRng = OsRng;

    let gens_1 = MultiCommitGens::new(1, b"test-productproof");
    let x = Scalar::random(&mut csprng);
    let rX = Scalar::random(&mut csprng);
    let y = Scalar::random(&mut csprng);
    let rY = Scalar::random(&mut csprng);
    let z = x * y;
    let rZ = Scalar::random(&mut csprng);
    let b1 = Scalar::random(&mut csprng);
    let b2 = Scalar::random(&mut csprng);
    let b3 = Scalar::random(&mut csprng);
    let b4 = Scalar::random(&mut csprng);
    let b5 = Scalar::random(&mut csprng);

    let mut prover_transcript = Transcript::new(b"example");
    let (proof, X, Y, Z) = ProductProof::prove(
      &gens_1,
      &mut prover_transcript,
      &x,
      &rX,
      &y,
      &rY,
      &z,
      &rZ,
      &b1,
      &b2,
      &b3,
      &b4,
      &b5,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &mut verifier_transcript, &X, &Y, &Z)
      .is_ok());
  }

  #[test]
  fn check_dotproductproof() {
    let mut csprng: OsRng = OsRng;

    let n = 1024;

    let gens_1 = MultiCommitGens::new(1, b"test-two");
    let gens_1024 = MultiCommitGens::new(n, b"test-1024");

    let mut x: Vec<Scalar> = Vec::new();
    let mut a: Vec<Scalar> = Vec::new();
    let mut d: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      x.push(Scalar::random(&mut csprng));
      a.push(Scalar::random(&mut csprng));
      d.push(Scalar::random(&mut csprng));
    }
    let y = DotProductProofLog::compute_dotproduct(&x, &a);
    let r_x = Scalar::random(&mut csprng);
    let r_y = Scalar::random(&mut csprng);
    let r_delta = Scalar::random(&mut csprng);
    let r_beta = Scalar::random(&mut csprng);

    let mut prover_transcript = Transcript::new(b"example");
    let (proof, Cx, Cy) = DotProductProof::prove(
      n,
      &gens_1,
      &gens_1024,
      &mut prover_transcript,
      &x,
      &r_x,
      &a,
      &y,
      &r_y,
      &d,
      &r_delta,
      &r_beta,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &gens_1024, &mut verifier_transcript, &a, &Cx, &Cy)
      .is_ok());
  }

  #[test]
  fn check_dotproductproof_log() {
    let mut csprng: OsRng = OsRng;

    let n = 1024;

    let gens = DotProductProofGens::new(n, b"test-1024");

    let x: Vec<Scalar> = (0..n).map(|_i| Scalar::random(&mut csprng)).collect();
    let a: Vec<Scalar> = (0..n).map(|_i| Scalar::random(&mut csprng)).collect();
    let y = DotProductProof::compute_dotproduct(&x, &a);

    let r_x = Scalar::random(&mut csprng);
    let r_y = Scalar::random(&mut csprng);
    let r_delta = Scalar::random(&mut csprng);
    let r_beta = Scalar::random(&mut csprng);
    let d = Scalar::random(&mut csprng);
    let blinds_vec = (0..2 * n.log2())
      .map(|_i| (Scalar::random(&mut csprng), Scalar::random(&mut csprng)))
      .collect();

    let mut prover_transcript = Transcript::new(b"example");
    let (proof, Cx, Cy) = DotProductProofLog::prove(
      n,
      &gens,
      &mut prover_transcript,
      &x,
      &r_x,
      &a,
      &y,
      &r_y,
      &d,
      &r_delta,
      &r_beta,
      &blinds_vec,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(n, &gens, &mut verifier_transcript, &a, &Cx, &Cy)
      .is_ok());
  }
}
