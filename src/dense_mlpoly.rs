use super::commitments::{Commitments, MultiCommitGens};
use super::errors::ProofVerifyError;
use super::math::Math;
use super::nizk::DotProductProof;
use super::scalar::{Scalar, ScalarBytesFromScalar};
use super::transcript::{AppendToTranscript, ProofTranscript};
use core::ops::Index;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use std::clone::Clone;

#[cfg(feature = "rayon_par")]
use rayon::prelude::*;

#[derive(Debug)]
pub struct DensePolynomial<T> {
  num_vars: usize, //the number of variables in the multilinear polynomial
  len: usize,
  Z: Vec<T>, // a vector that holds the evaluations of the polynomial in all the 2^num_vars Boolean inputs
}

pub struct DensePolynomialSize {
  num_vars: usize,
}

pub struct PolyCommitmentGens {
  gens_1: MultiCommitGens,
  gens_m: MultiCommitGens,
}

impl PolyCommitmentGens {
  // the number of variables in the multilinear polynomial
  pub fn new(size: &DensePolynomialSize, label: &'static [u8]) -> PolyCommitmentGens {
    let m = size.num_vars.pow2().square_root();
    let gens_1 = MultiCommitGens::new(1, label);
    let gens_m = MultiCommitGens::new(m, label);
    PolyCommitmentGens { gens_1, gens_m }
  }
}

pub struct PolyCommitmentBlinds {
  blinds: Vec<Scalar>,
}

impl PolyCommitmentBlinds {
  // the number of variables in the multilinear polynomial
  pub fn new(size: &DensePolynomialSize, csprng: &mut OsRng) -> PolyCommitmentBlinds {
    let m = size.num_vars.pow2().square_root();
    let blinds = (0..m)
      .collect::<Vec<usize>>()
      .iter()
      .map(|&_i| Scalar::random(csprng))
      .collect::<Vec<Scalar>>();
    PolyCommitmentBlinds { blinds }
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PolyCommitment {
  C: Vec<CompressedRistretto>,
}

pub struct EqPolynomial {
  r: Vec<Scalar>,
}

impl EqPolynomial {
  pub fn new(r: Vec<Scalar>) -> Self {
    EqPolynomial { r }
  }

  pub fn evals(&self) -> Vec<Scalar> {
    let ell = self.r.len();

    let mut evals: Vec<Scalar> = vec![Scalar::one(); ell.pow2()];
    let mut size = 1;
    for j in 0..ell {
      // in each iteration, we double the size of chis
      size = size * 2;
      for i in (0..size).rev().step_by(2) {
        // copy each element from the prior iteration twice
        let scalar = evals[i / 2];
        //                evals[i - 1] = scalar * (Scalar::one() - tau[j]);
        //                evals[i] = scalar * tau[j];
        evals[i] = scalar * self.r[j];
        evals[i - 1] = scalar - evals[i];
      }
    }
    evals
  }

  pub fn compute_factored_evals(&self) -> (Vec<Scalar>, Vec<Scalar>) {
    let ell = self.r.len();
    // ensure ell is even
    assert!(ell % 2 == 0);

    let L = EqPolynomial::new(self.r[0..ell / 2].to_vec()).evals();
    let R = EqPolynomial::new(self.r[ell / 2..ell].to_vec()).evals();

    (L, R)
  }
}

pub trait DensePolynomialTrait {
  type Item;

  fn new(Z: Vec<Self::Item>) -> DensePolynomial<Self::Item>;
  fn get_num_vars(&self) -> usize;
  fn size(&self) -> DensePolynomialSize;
  fn len(&self) -> usize;
  fn clone(&self) -> DensePolynomial<Self::Item>;
  fn split(&self, idx: usize) -> (DensePolynomial<Self::Item>, DensePolynomial<Self::Item>);
  fn commit(&self, blinds: &PolyCommitmentBlinds, gens: &PolyCommitmentGens) -> PolyCommitment;
}

// TODO: combine the two traits
pub trait DensePolynomialBoundTrait {
  fn bound(&self, L: &Vec<Scalar>) -> Vec<Scalar>;
}

#[allow(dead_code)]
//impl<T> DensePolynomial<T>
impl<T> DensePolynomialTrait for DensePolynomial<T>
where
  T: Clone,
  [T]: Commitments,
  T: std::marker::Sync,
{
  type Item = T;
  fn new(Z: Vec<T>) -> Self {
    let len = Z.len();
    let num_vars = len.log2();
    DensePolynomial::<T> { num_vars, Z, len }
  }

  fn get_num_vars(&self) -> usize {
    self.num_vars
  }

  fn size(&self) -> DensePolynomialSize {
    DensePolynomialSize {
      num_vars: self.num_vars,
    }
  }

  fn len(&self) -> usize {
    self.len
  }

  fn clone(&self) -> DensePolynomial<T> {
    DensePolynomial::<T>::new(self.Z[0..self.len].to_vec())
  }

  fn split(&self, idx: usize) -> (DensePolynomial<T>, DensePolynomial<T>) {
    assert!(idx < self.len());
    (
      DensePolynomial::<T>::new(self.Z[0..idx].to_vec()),
      DensePolynomial::<T>::new(self.Z[idx..2 * idx].to_vec()),
    )
  }

  #[cfg(feature = "rayon_par")]
  fn commit(&self, blinds: &PolyCommitmentBlinds, gens: &PolyCommitmentGens) -> PolyCommitment {
    let n = self.Z.len();
    let m = n.square_root();
    assert_eq!(m * m, n); // check if Z's size if a perfect square
    assert_eq!(blinds.blinds.len(), m);

    let C = (0..m)
      .collect::<Vec<usize>>()
      .par_iter()
      .map(|&i| {
        self.Z[m * i..m * (i + 1)]
          .commit(&blinds.blinds[i], &gens.gens_m)
          .compress()
      })
      .collect();
    PolyCommitment { C }
  }

  #[cfg(not(feature = "rayon_par"))]
  fn commit(&self, blinds: &PolyCommitmentBlinds, gens: &PolyCommitmentGens) -> PolyCommitment {
    let n = self.Z.len();
    let m = n.square_root();
    assert_eq!(m * m, n); // check if Z's size if a perfect square
    assert_eq!(blinds.blinds.len(), m);

    let C = (0..m)
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| {
        (&self.Z[m * i..m * (i + 1)])
          .commit(&blinds.blinds[i], &gens.gens_m)
          .compress()
      })
      .collect();

    PolyCommitment { C }
  }
}

impl DensePolynomialBoundTrait for DensePolynomial<Scalar> {
  fn bound(&self, L: &Vec<Scalar>) -> Vec<Scalar> {
    let m = self.len().square_root();
    (0..m)
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| {
        (0..m)
          .collect::<Vec<usize>>()
          .iter()
          .map(|&j| &L[j] * &self.Z[j * m + i])
          .sum()
      })
      .collect::<Vec<Scalar>>()
  }
}

impl DensePolynomialBoundTrait for DensePolynomial<bool> {
  fn bound(&self, L: &Vec<Scalar>) -> Vec<Scalar> {
    let m = self.len().square_root();
    (0..m)
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| {
        let mut res = Scalar::zero();
        for j in 0..m {
          if self.Z[j * m + i] {
            res = &res + &L[j];
          }
        }
        res
      })
      .collect::<Vec<Scalar>>()
  }
}

impl DensePolynomial<Scalar> {
  pub fn bound_poly_var_top(&mut self, r: &Scalar) {
    let n = self.len() / 2;
    for i in 0..n {
      self.Z[i] = &self.Z[i] + r * (&self.Z[i + n] - &self.Z[i]);
    }
    self.num_vars = self.num_vars - 1;
    self.len = n;
  }

  pub fn bound_poly_var_bot(&mut self, r: &Scalar) {
    let n = self.len() / 2;
    for i in 0..n {
      self.Z[i] = &self.Z[2 * i] + r * (&self.Z[2 * i + 1] - &self.Z[2 * i]);
    }
    self.num_vars = self.num_vars - 1;
    self.len = n;
  }

  pub fn dotproduct(&self, other: &DensePolynomial<Scalar>) -> Scalar {
    assert_eq!(self.len(), other.len());
    let mut res = Scalar::zero();
    for i in 0..self.len() {
      res = &res + &self.Z[i] * &other[i];
    }
    res
  }

  // returns Z(r) in O(n) time
  pub fn evaluate(&self, r: &Vec<Scalar>) -> Scalar {
    // r must have a value for each variable
    assert_eq!(r.len(), self.get_num_vars());
    let chis = EqPolynomial::new(r.to_vec()).evals();
    assert_eq!(chis.len(), self.Z.len());
    DotProductProof::compute_dotproduct(&self.Z, &chis)
  }

  fn vec(&self) -> &Vec<Scalar> {
    &self.Z
  }

  pub fn extend(&mut self, other: &DensePolynomial<Scalar>) {
    // TODO: allow extension even when some vars are bound
    assert_eq!(self.Z.len(), self.len);
    let other_vec = other.vec();
    assert_eq!(other_vec.len(), self.Z.len());
    self.Z.extend(other_vec);
    self.num_vars = self.num_vars + 1;
    self.len = 2 * self.len;
    assert_eq!(self.Z.len(), self.len);
  }
}

impl DensePolynomial<bool> {
  pub fn bound_poly_var_bot(&self, r: &Scalar) -> DensePolynomial<Scalar> {
    let n = self.len() / 2;
    let one_minus_r = Scalar::one() - r;
    let mut Z_bound: Vec<Scalar> = vec![Scalar::zero(); n];
    for i in 0..n {
      Z_bound[i] = match (self.Z[2 * i], self.Z[2 * i + 1]) {
        (false, false) => Scalar::zero(),
        (false, true) => *r,
        (true, false) => one_minus_r,
        (true, true) => Scalar::one(),
      };
    }
    DensePolynomial::<Scalar>::new(Z_bound)
  }
}

impl<T> Index<usize> for DensePolynomial<T> {
  type Output = T;

  #[inline(always)]
  fn index(&self, _index: usize) -> &T {
    &(self.Z[_index])
  }
}

impl AppendToTranscript for PolyCommitment {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, b"poly_commitment_begin");
    for i in 0..self.C.len() {
      transcript.append_point(b"poly_commitment_share", &self.C[i]);
    }
    transcript.append_message(label, b"poly_commitment_end");
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PolyEvalProof {
  proof: DotProductProof,
}

#[allow(dead_code)]
impl PolyEvalProof {
  fn protocol_name() -> &'static [u8] {
    b"polynomial evaluation proof"
  }

  pub fn prove<T>(
    poly: &DensePolynomial<T>,
    comm: &PolyCommitment,
    blinds: &PolyCommitmentBlinds,
    r: &Vec<Scalar>, // point at which the polynomial is evaluated
    Zr: Scalar,      // evaluation of \widetilde{Z}(r)
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
  ) -> (PolyEvalProof, CompressedRistretto)
  where
    T: Clone,
    [T]: Commitments,
    DensePolynomial<T>: DensePolynomialTrait + DensePolynomialBoundTrait,
  {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());

    // assert vectors are of the right size
    assert_eq!(poly.get_num_vars(), r.len());
    let n = r.len().pow2();
    let m = n.square_root();
    assert_eq!(comm.C.len(), m);
    assert_eq!(blinds.blinds.len(), m);

    let mut csprng: OsRng = OsRng;

    // compute the L and R vectors
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();

    // compute the vector underneath L*Z and the L*blinds
    // compute vector-matrix product between L and Z viewed as a matrix
    let LZ = poly.bound(&L);

    let LZ_blind = (0..m)
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| blinds.blinds[i] * L[i])
      .sum();

    // compute blind for committing Zr
    let r_Zr = Scalar::random(&mut csprng); // TODO: take this as input from the caller so prove is deterministc
    let d = (0..m)
      .collect::<Vec<usize>>()
      .iter()
      .map(|&_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    let r_delta = Scalar::random(&mut csprng); // TODO: take this as input from the caller so prove is deterministc
    let r_beta = Scalar::random(&mut csprng); // TODO: take this as input from the caller so prove is deterministc

    let (proof, _C_LR, C_Zr_prime) = DotProductProof::prove(
      m,
      &gens.gens_1,
      &gens.gens_m,
      transcript,
      &LZ,
      LZ_blind,
      &R,
      Zr,
      r_Zr,
      &d,
      r_delta,
      r_beta,
    );

    (PolyEvalProof { proof }, C_Zr_prime)
  }

  pub fn verify(
    &self,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    r: &Vec<Scalar>,           // point at which the polynomial is evaluated
    C_Zr: CompressedRistretto, // commitment to \widetilde{Z}(r)
    comm: &PolyCommitment,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());

    // compute L and R
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();

    // compute a weighted sum of commitments and L
    let C_decompressed = comm.C.iter().map(|pt| pt.decompress().unwrap());
    let C_LZ = RistrettoPoint::vartime_multiscalar_mul(Scalar::decompress_vec(&L), C_decompressed)
      .compress();

    self
      .proof
      .verify(&gens.gens_1, &gens.gens_m, transcript, &R, C_LZ, C_Zr)
  }
}

#[cfg(test)]
mod tests {
  use super::super::scalar::ScalarFromPrimitives;
  use super::*;

  fn evaluate_with_LR(Z: &Vec<Scalar>, r: &Vec<Scalar>) -> Scalar {
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();

    let ell = r.len();
    // ensure ell is even
    assert!(ell % 2 == 0);
    // compute n = 2^\ell
    let n = ell.pow2();
    // compute m = sqrt(n) = 2^{\ell/2}
    let m = n.square_root();

    // compute vector-matrix product between L and Z viewed as a matrix
    let LZ = (0..m)
      .collect::<Vec<usize>>()
      .iter()
      .map(|&i| {
        (0..m)
          .collect::<Vec<usize>>()
          .iter()
          .map(|&j| L[j] * Z[j * m + i])
          .sum()
      })
      .collect::<Vec<Scalar>>();

    // compute dot product between LZ and R
    DotProductProof::compute_dotproduct(&LZ, &R)
  }

  #[test]
  fn check_polynomial_evaluation() {
    let mut Z: Vec<Scalar> = Vec::new(); // Z = [1, 2, 1, 4]
    Z.push(Scalar::one());
    Z.push((2 as usize).to_scalar());
    Z.push((1 as usize).to_scalar());
    Z.push((4 as usize).to_scalar());
    // r = [4,3]
    let mut r: Vec<Scalar> = Vec::new();
    r.push((4 as usize).to_scalar());
    r.push((3 as usize).to_scalar());

    let eval_with_LR = evaluate_with_LR(&Z, &r);
    let poly = DensePolynomial::new(Z);

    let eval = poly.evaluate(&r);
    assert_eq!(eval, (28 as usize).to_scalar());
    assert_eq!(eval_with_LR, eval);
  }

  pub fn compute_factored_chis_at_r(r: &Vec<Scalar>) -> (Vec<Scalar>, Vec<Scalar>) {
    let mut L: Vec<Scalar> = Vec::new();
    let mut R: Vec<Scalar> = Vec::new();

    let ell = r.len();
    assert!(ell % 2 == 0); // ensure ell is even
    let n = ell.pow2();
    let m = n.square_root();

    // compute row vector L
    for i in 0..m {
      let mut chi_i = Scalar::one();
      for j in 0..ell / 2 {
        let bit_j = ((m * i) & (1 << (r.len() - j - 1))) > 0;
        if bit_j {
          chi_i *= r[j];
        } else {
          chi_i *= Scalar::one() - r[j];
        }
      }
      L.push(chi_i);
    }

    // compute column vector R
    for i in 0..m {
      let mut chi_i = Scalar::one();
      for j in ell / 2..ell {
        let bit_j = (i & (1 << (r.len() - j - 1))) > 0;
        if bit_j {
          chi_i *= r[j];
        } else {
          chi_i *= Scalar::one() - r[j];
        }
      }
      R.push(chi_i);
    }
    (L, R)
  }

  pub fn compute_chis_at_r(r: &Vec<Scalar>) -> Vec<Scalar> {
    let ell = r.len();
    let n = ell.pow2();
    let mut chis: Vec<Scalar> = Vec::new();
    for i in 0..n {
      let mut chi_i = Scalar::one();
      for j in 0..r.len() {
        let bit_j = (i & (1 << (r.len() - j - 1))) > 0;
        if bit_j {
          chi_i *= r[j];
        } else {
          chi_i *= Scalar::one() - r[j];
        }
      }
      chis.push(chi_i);
    }
    chis
  }

  pub fn compute_outerproduct(L: Vec<Scalar>, R: Vec<Scalar>) -> Vec<Scalar> {
    assert_eq!(L.len(), R.len());

    let mut O: Vec<Scalar> = Vec::new();
    let m = L.len();
    for i in 0..m {
      for j in 0..m {
        O.push(L[i] * R[j]);
      }
    }
    O
  }

  #[test]
  fn check_memoized_chis() {
    let mut csprng: OsRng = OsRng;

    let s = 10;
    let mut r: Vec<Scalar> = Vec::new();
    for _i in 0..s {
      r.push(Scalar::random(&mut csprng));
    }
    let chis = tests::compute_chis_at_r(&r);
    let chis_m = EqPolynomial::new(r).evals();
    assert_eq!(chis, chis_m);
  }

  #[test]
  fn check_factored_chis() {
    let mut csprng: OsRng = OsRng;

    let s = 10;
    let mut r: Vec<Scalar> = Vec::new();
    for _i in 0..s {
      r.push(Scalar::random(&mut csprng));
    }
    let chis = EqPolynomial::new(r.clone()).evals();
    let (L, R) = EqPolynomial::new(r).compute_factored_evals();
    let O = compute_outerproduct(L, R);
    assert_eq!(chis, O);
  }

  #[test]
  fn check_memoized_factored_chis() {
    let mut csprng: OsRng = OsRng;

    let s = 10;
    let mut r: Vec<Scalar> = Vec::new();
    for _i in 0..s {
      r.push(Scalar::random(&mut csprng));
    }
    let (L, R) = tests::compute_factored_chis_at_r(&r);
    let eq = EqPolynomial::new(r);
    let (L2, R2) = eq.compute_factored_evals();
    assert_eq!(L, L2);
    assert_eq!(R, R2);
  }

  #[test]
  fn check_polynomial_commit() {
    let mut Z: Vec<Scalar> = Vec::new(); // Z = [1, 2, 1, 4]
    Z.push((1 as usize).to_scalar());
    Z.push((2 as usize).to_scalar());
    Z.push((1 as usize).to_scalar());
    Z.push((4 as usize).to_scalar());

    let poly = DensePolynomial::new(Z);

    // r = [4,3]
    let mut r: Vec<Scalar> = Vec::new();
    r.push((4 as usize).to_scalar());
    r.push((3 as usize).to_scalar());
    let eval = poly.evaluate(&r);
    assert_eq!(eval, (28 as usize).to_scalar());

    let gens = PolyCommitmentGens::new(&poly.size(), b"test-two");
    let mut csprng: OsRng = OsRng;
    let blinds = PolyCommitmentBlinds::new(&poly.size(), &mut csprng);

    let poly_commitment = poly.commit(&blinds, &gens);

    let mut prover_transcript = Transcript::new(b"example");
    let (proof, C_Zr) = PolyEvalProof::prove(
      &poly,
      &poly_commitment,
      &blinds,
      &r,
      eval,
      &gens,
      &mut prover_transcript,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens, &mut verifier_transcript, &r, C_Zr, &poly_commitment)
      .is_ok());
  }
}
