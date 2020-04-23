use super::commitments::{Commitments, MultiCommitGens};
use super::errors::ProofVerifyError;
use super::math::Math;
use super::nizk::{DotProductProofGens, DotProductProofLog};
use super::scalar::{Scalar, ScalarBytesFromScalar};
use super::transcript::{AppendToTranscript, ProofTranscript};
use core::ops::Index;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

#[cfg(feature = "rayon_par")]
use rayon::prelude::*;

#[derive(Debug)]
pub struct DensePolynomial {
  num_vars: usize, //the number of variables in the multilinear polynomial
  len: usize,
  Z: Vec<Scalar>, // a vector that holds the evaluations of the polynomial in all the 2^num_vars Boolean inputs
}

pub struct PolyCommitmentGens {
  pub gens: DotProductProofGens,
}

impl PolyCommitmentGens {
  // the number of variables in the multilinear polynomial
  pub fn new(num_vars: usize, label: &'static [u8]) -> PolyCommitmentGens {
    let (_left, right) = EqPolynomial::compute_factored_lens(num_vars);
    let gens = DotProductProofGens::new(right.pow2(), label);
    PolyCommitmentGens { gens }
  }
}

pub struct PolyCommitmentBlinds {
  blinds: Vec<Scalar>,
}

impl PolyCommitmentBlinds {
  // the number of variables in the multilinear polynomial
  pub fn new(num_vars: usize, csprng: &mut OsRng) -> PolyCommitmentBlinds {
    let (left, _right) = EqPolynomial::compute_factored_lens(num_vars);
    let blinds = (0..left.pow2())
      .map(|_i| Scalar::random(csprng))
      .collect::<Vec<Scalar>>();
    PolyCommitmentBlinds { blinds }
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PolyCommitment {
  C: Vec<CompressedRistretto>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ConstPolyCommitment {
  C: CompressedRistretto,
}

impl PolyCommitment {
  pub fn combine(&self, comm: &PolyCommitment, s: &Scalar) -> PolyCommitment {
    assert_eq!(comm.C.len(), self.C.len());
    let C = (0..self.C.len())
      .map(|i| {
        (self.C[i].decompress().unwrap()
          + Scalar::decompress_scalar(s) * comm.C[i].decompress().unwrap())
        .compress()
      })
      .collect::<Vec<CompressedRistretto>>();
    PolyCommitment { C }
  }

  pub fn combine_const(&self, comm: &ConstPolyCommitment) -> PolyCommitment {
    let C = (0..self.C.len())
      .map(|i| (self.C[i].decompress().unwrap() + comm.C.decompress().unwrap()).compress())
      .collect::<Vec<CompressedRistretto>>();
    PolyCommitment { C }
  }
}

pub struct EqPolynomial {
  r: Vec<Scalar>,
}

impl EqPolynomial {
  pub fn new(r: Vec<Scalar>) -> Self {
    EqPolynomial { r }
  }

  pub fn evaluate(&self, rx: &Vec<Scalar>) -> Scalar {
    assert_eq!(self.r.len(), rx.len());
    (0..rx.len())
      .map(|i| self.r[i] * rx[i] + (Scalar::one() - self.r[i]) * (Scalar::one() - rx[i]))
      .product()
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

  pub fn compute_factored_lens(ell: usize) -> (usize, usize) {
    (ell / 2, ell - ell / 2)
  }

  pub fn compute_factored_evals(&self) -> (Vec<Scalar>, Vec<Scalar>) {
    let ell = self.r.len();
    let (left_num_vars, _right_num_vars) = EqPolynomial::compute_factored_lens(ell);

    let L = EqPolynomial::new(self.r[0..left_num_vars].to_vec()).evals();
    let R = EqPolynomial::new(self.r[left_num_vars..ell].to_vec()).evals();

    (L, R)
  }
}

pub struct ConstPolynomial {
  num_vars: usize,
  c: Scalar,
}

impl ConstPolynomial {
  pub fn new(num_vars: usize, c: Scalar) -> Self {
    ConstPolynomial { num_vars, c }
  }

  pub fn evaluate(&self, rx: &Vec<Scalar>) -> Scalar {
    assert_eq!(self.num_vars, rx.len());
    self.c
  }

  pub fn get_num_vars(&self) -> usize {
    self.num_vars
  }

  /// produces a binding commitment
  pub fn commit(&self, gens: &PolyCommitmentGens) -> PolyCommitment {
    let ell = self.get_num_vars();

    let (left_num_vars, right_num_vars) = EqPolynomial::compute_factored_lens(ell);
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();
    assert_eq!(L_size * R_size, ell.pow2());

    let vec = vec![self.c; R_size];

    let c = vec.commit(&Scalar::zero(), &gens.gens.gens_n).compress();
    PolyCommitment { C: vec![c; L_size] }
  }
}

pub struct IdentityPolynomial {
  size_point: usize,
}

impl IdentityPolynomial {
  pub fn new(size_point: usize) -> Self {
    IdentityPolynomial { size_point }
  }

  pub fn evaluate(&self, r: &Vec<Scalar>) -> Scalar {
    let len = r.len();
    assert_eq!(len, self.size_point);
    (0..len)
      .map(|i| Scalar::from((len - i - 1).pow2() as u64) * r[i])
      .sum()
  }
}

#[allow(dead_code)]
impl DensePolynomial {
  pub fn new(Z: Vec<Scalar>) -> Self {
    let len = Z.len();
    let num_vars = len.log2();
    DensePolynomial { num_vars, Z, len }
  }

  pub fn get_num_vars(&self) -> usize {
    self.num_vars
  }

  pub fn len(&self) -> usize {
    self.len
  }

  pub fn clone(&self) -> DensePolynomial {
    DensePolynomial::new(self.Z[0..self.len].to_vec())
  }

  pub fn split(&self, idx: usize) -> (DensePolynomial, DensePolynomial) {
    assert!(idx < self.len());
    (
      DensePolynomial::new(self.Z[0..idx].to_vec()),
      DensePolynomial::new(self.Z[idx..2 * idx].to_vec()),
    )
  }

  #[cfg(feature = "rayon_par")]
  fn commit_inner(&self, blinds: &Vec<Scalar>, gens: &MultiCommitGens) -> PolyCommitment {
    let L_size = blinds.len();
    let R_size = self.Z.len() / L_size;
    assert_eq!(L_size * R_size, self.Z.len());
    let C = (0..L_size)
      .collect::<Vec<usize>>()
      .par_iter()
      .map(|&i| {
        self.Z[R_size * i..R_size * (i + 1)]
          .commit(&blinds[i], gens)
          .compress()
      })
      .collect();
    PolyCommitment { C }
  }

  #[cfg(not(feature = "rayon_par"))]
  fn commit_inner(&self, blinds: &Vec<Scalar>, gens: &MultiCommitGens) -> PolyCommitment {
    let L_size = blinds.len();
    let R_size = self.Z.len() / L_size;
    assert_eq!(L_size * R_size, self.Z.len());
    let C = (0..L_size)
      .map(|i| {
        self.Z[R_size * i..R_size * (i + 1)]
          .commit(&blinds[i], gens)
          .compress()
      })
      .collect();
    PolyCommitment { C }
  }

  pub fn commit(
    &self,
    blinds_opt: Option<&PolyCommitmentBlinds>,
    gens: &PolyCommitmentGens,
  ) -> PolyCommitment {
    let n = self.Z.len();
    let ell = self.get_num_vars();
    assert_eq!(n, ell.pow2());

    let (left_num_vars, right_num_vars) = EqPolynomial::compute_factored_lens(ell);
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();
    assert_eq!(L_size * R_size, n);

    let default_blinds = PolyCommitmentBlinds {
      blinds: vec![Scalar::zero(); L_size],
    };
    let blinds = match blinds_opt {
      Some(p) => p,
      None => &default_blinds,
    };

    assert_eq!(blinds.blinds.len(), L_size);

    self.commit_inner(&blinds.blinds, &gens.gens.gens_n)
  }

  pub fn bound(&self, L: &Vec<Scalar>) -> Vec<Scalar> {
    let (left_num_vars, right_num_vars) = EqPolynomial::compute_factored_lens(self.get_num_vars());
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();
    (0..R_size)
      .map(|i| (0..L_size).map(|j| &L[j] * &self.Z[j * R_size + i]).sum())
      .collect::<Vec<Scalar>>()
  }

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

  pub fn dotproduct(&self, other: &DensePolynomial) -> Scalar {
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
    DotProductProofLog::compute_dotproduct(&self.Z, &chis)
  }

  fn vec(&self) -> &Vec<Scalar> {
    &self.Z
  }

  pub fn extend(&mut self, other: &DensePolynomial) {
    // TODO: allow extension even when some vars are bound
    assert_eq!(self.Z.len(), self.len);
    let other_vec = other.vec();
    assert_eq!(other_vec.len(), self.len);
    self.Z.extend(other_vec);
    self.num_vars = self.num_vars + 1;
    self.len = 2 * self.len;
    assert_eq!(self.Z.len(), self.len);
  }

  pub fn merge<'a, I>(polys: I) -> DensePolynomial
  where
    I: IntoIterator<Item = &'a DensePolynomial>,
  {
    //assert!(polys.len() > 0);
    //let num_vars = polys[0].num_vars();
    let mut Z: Vec<Scalar> = Vec::new();
    for poly in polys.into_iter() {
      //assert_eq!(poly.get_num_vars(), num_vars); // ensure each polynomial has the same number of variables
      //assert_eq!(poly.len, poly.vec().len()); // ensure no variable is already bound
      Z.extend(poly.vec());
    }

    // pad the polynomial with zero polynomial at the end
    Z.resize(Z.len().next_power_of_two(), Scalar::zero());

    DensePolynomial::new(Z)
  }

  pub fn from_usize(Z: &Vec<usize>) -> Self {
    DensePolynomial::new(
      (0..Z.len())
        .map(|i| Scalar::from(Z[i] as u64))
        .collect::<Vec<Scalar>>(),
    )
  }
}

impl Index<usize> for DensePolynomial {
  type Output = Scalar;

  #[inline(always)]
  fn index(&self, _index: usize) -> &Scalar {
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
  proof: DotProductProofLog,
}

#[allow(dead_code)]
impl PolyEvalProof {
  fn protocol_name() -> &'static [u8] {
    b"polynomial evaluation proof"
  }

  pub fn prove(
    poly: &DensePolynomial,
    blinds_opt: Option<&PolyCommitmentBlinds>,
    r: &Vec<Scalar>,               // point at which the polynomial is evaluated
    Zr: &Scalar,                   // evaluation of \widetilde{Z}(r)
    blind_Zr_opt: Option<&Scalar>, // blind for commitment to \widetilde{Z}(r)
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
  ) -> (PolyEvalProof, CompressedRistretto) {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());

    // assert vectors are of the right size
    assert_eq!(poly.get_num_vars(), r.len());

    let (left_num_vars, right_num_vars) = EqPolynomial::compute_factored_lens(r.len());
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();

    let default_blinds = PolyCommitmentBlinds {
      blinds: vec![Scalar::zero(); L_size],
    };
    let blinds = match blinds_opt {
      Some(p) => p,
      None => &default_blinds,
    };

    let zero = Scalar::zero();
    let blind_Zr = match blind_Zr_opt {
      Some(p) => p,
      None => &zero,
    };

    assert_eq!(blinds.blinds.len(), L_size);

    let mut csprng: OsRng = OsRng;

    // compute the L and R vectors
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();
    assert_eq!(L.len(), L_size);
    assert_eq!(R.len(), R_size);

    // compute the vector underneath L*Z and the L*blinds
    // compute vector-matrix product between L and Z viewed as a matrix
    let LZ = poly.bound(&L);
    let LZ_blind: Scalar = (0..L.len()).map(|i| blinds.blinds[i] * L[i]).sum();

    let d = Scalar::random(&mut csprng);
    let r_delta = Scalar::random(&mut csprng); // TODO: take this as input from the caller so prove is deterministc
    let r_beta = Scalar::random(&mut csprng); // TODO: take this as input from the caller so prove is deterministc
    let blinds_vec = (0..2 * R_size.log2())
      .map(|_i| (Scalar::random(&mut csprng), Scalar::random(&mut csprng)))
      .collect();
    let (proof, _C_LR, C_Zr_prime) = DotProductProofLog::prove(
      R_size,
      &gens.gens,
      transcript,
      &LZ,
      &LZ_blind,
      &R,
      &Zr,
      blind_Zr,
      &d,
      &r_delta,
      &r_beta,
      &blinds_vec,
    );

    (PolyEvalProof { proof }, C_Zr_prime)
  }

  pub fn verify(
    &self,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    r: &Vec<Scalar>,            // point at which the polynomial is evaluated
    C_Zr: &CompressedRistretto, // commitment to \widetilde{Z}(r)
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
      .verify(R.len(), &gens.gens, transcript, &R, &C_LZ, C_Zr)
  }

  pub fn verify_batched(
    &self,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    r: &Vec<Scalar>,            // point at which the polynomial is evaluated
    C_Zr: &CompressedRistretto, // commitment to \widetilde{Z}(r)
    comm: &[&PolyCommitment],
    coeff: &[&Scalar],
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());

    // compute L and R
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();

    // compute a weighted sum of commitments and L
    let C_decompressed: Vec<Vec<RistrettoPoint>> = (0..comm.len())
      .map(|i| {
        comm[i]
          .C
          .iter()
          .map(|pt| pt.decompress().unwrap())
          .collect()
      })
      .collect();

    let C_LZ: Vec<RistrettoPoint> = (0..comm.len())
      .map(|i| {
        RistrettoPoint::vartime_multiscalar_mul(Scalar::decompress_vec(&L), &C_decompressed[i])
      })
      .collect();

    let C_LZ_combined: RistrettoPoint = (0..C_LZ.len())
      .map(|i| C_LZ[i] * Scalar::decompress_scalar(&coeff[i]))
      .sum();

    self.proof.verify(
      R.len(),
      &gens.gens,
      transcript,
      &R,
      &C_LZ_combined.compress(),
      C_Zr,
    )
  }

  pub fn verify_plain(
    &self,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    r: &Vec<Scalar>, // point at which the polynomial is evaluated
    Zr: &Scalar,     // evaluation \widetilde{Z}(r)
    comm: &PolyCommitment,
  ) -> Result<(), ProofVerifyError> {
    // compute a commitment to Zr with a blind of zero
    let C_Zr = Zr.commit(&Scalar::zero(), &gens.gens.gens_1).compress();

    self.verify(gens, transcript, r, &C_Zr, comm)
  }

  pub fn verify_plain_batched(
    &self,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    r: &Vec<Scalar>, // point at which the polynomial is evaluated
    Zr: &Scalar,     // evaluation \widetilde{Z}(r)
    comm: &[&PolyCommitment],
    coeff: &[&Scalar],
  ) -> Result<(), ProofVerifyError> {
    // compute a commitment to Zr with a blind of zero
    let C_Zr = Zr.commit(&Scalar::zero(), &gens.gens.gens_1).compress();

    assert_eq!(comm.len(), coeff.len());

    self.verify_batched(gens, transcript, r, &C_Zr, comm, coeff)
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
      .map(|i| (0..m).map(|j| L[j] * Z[j * m + i]).sum())
      .collect::<Vec<Scalar>>();

    // compute dot product between LZ and R
    DotProductProofLog::compute_dotproduct(&LZ, &R)
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

    let gens = PolyCommitmentGens::new(poly.get_num_vars(), b"test-two");
    let mut csprng: OsRng = OsRng;
    let blinds = PolyCommitmentBlinds::new(poly.get_num_vars(), &mut csprng);

    let poly_commitment = poly.commit(Some(&blinds), &gens);

    let mut prover_transcript = Transcript::new(b"example");
    let (proof, C_Zr) = PolyEvalProof::prove(
      &poly,
      Some(&blinds),
      &r,
      &eval,
      None,
      &gens,
      &mut prover_transcript,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens, &mut verifier_transcript, &r, &C_Zr, &poly_commitment)
      .is_ok());
  }
}
