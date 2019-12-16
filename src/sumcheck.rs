use super::dense_mlpoly::{DensePolynomial, DensePolynomialTrait};
use super::errors::ProofVerifyError;
use super::scalar::Scalar;
use super::transcript::{AppendToTranscript, ProofTranscript};
use super::unipoly::SumcheckProofPolyABI;
use super::unipoly::{CubicPoly, QuadPoly};
use merlin::Transcript;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct SumcheckInstanceProof<T: SumcheckProofPolyABI + AppendToTranscript> {
  polys: Vec<T>,
}

impl<T: SumcheckProofPolyABI + AppendToTranscript> SumcheckInstanceProof<T> {
  pub fn new(polys: Vec<T>) -> SumcheckInstanceProof<T> {
    SumcheckInstanceProof { polys }
  }

  pub fn verify(
    &self,
    claim: Scalar,
    num_rounds: usize,
    transcript: &mut Transcript,
  ) -> Result<(Scalar, Vec<Scalar>), ProofVerifyError> {
    let mut e = claim;
    let mut r: Vec<Scalar> = Vec::new();
    for i in 0..num_rounds {
      let poly = &self.polys[i];

      // check if G_k(0) + G_k(1) = e
      if poly.eval_at_zero() + poly.eval_at_one() != e {
        println!("Randomness so far {:?}", r);
        assert_eq!(0, 1);
        return Err(ProofVerifyError);
      }

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_i = transcript.challenge_scalar(b"challenge_nextround");

      r.push(r_i);

      // evaluate the claimed degree-ell polynomial at r_i
      e = poly.evaluate(&r_i);
    }

    Ok((e, r))
  }
}

#[allow(dead_code)]
impl SumcheckInstanceProof<QuadPoly> {
  pub fn prove<F>(
    claim: &Scalar,
    num_rounds: usize,
    poly_A: &mut DensePolynomial<Scalar>,
    poly_B: &mut DensePolynomial<Scalar>,
    comb_func: F,
    transcript: &mut Transcript,
  ) -> (Self, Vec<Scalar>, Vec<Scalar>)
  where
    F: Fn(&Scalar, &Scalar) -> Scalar,
  {
    let mut e = *claim;
    let mut r: Vec<Scalar> = Vec::new();
    let mut quad_polys: Vec<QuadPoly> = Vec::new();
    for _j in 0..num_rounds {
      let mut eval_point_0 = Scalar::zero();
      let mut eval_point_2 = Scalar::zero();

      let len = poly_A.len() / 2;
      for i in 0..len {
        // eval 0: bound_func is A(low)
        eval_point_0 = &eval_point_0 + comb_func(&poly_A[i], &poly_B[i]);

        // eval 2: bound_func is -A(low) + 2*A(high)
        let poly_A_bound_point = &poly_A[len + i] + &poly_A[len + i] - &poly_A[i];
        let poly_B_bound_point = &poly_B[len + i] + &poly_B[len + i] - &poly_B[i];
        eval_point_2 = &eval_point_2 + comb_func(&poly_A_bound_point, &poly_B_bound_point);
      }

      let poly = QuadPoly::new(eval_point_0, e - eval_point_0, eval_point_2);

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");
      r.push(r_j);
      // bound all tables to the verifier's challenege
      poly_A.bound_poly_var_top(&r_j);
      poly_B.bound_poly_var_top(&r_j);
      e = poly.evaluate(&r_j);
      quad_polys.push(poly);
    }

    (
      SumcheckInstanceProof::new(quad_polys),
      r,
      vec![poly_A[0], poly_B[0]],
    )
  }
}

#[allow(dead_code)]
impl SumcheckInstanceProof<CubicPoly> {
  pub fn prove<F>(
    claim: &Scalar,
    num_rounds: usize,
    poly_A: &mut DensePolynomial<Scalar>,
    poly_B: &mut DensePolynomial<Scalar>,
    poly_C: &mut DensePolynomial<Scalar>,
    comb_func: F,
    transcript: &mut Transcript,
  ) -> (Self, Vec<Scalar>, Vec<Scalar>)
  where
    F: Fn(&Scalar, &Scalar, &Scalar) -> Scalar,
  {
    let mut e = *claim;
    let mut r: Vec<Scalar> = Vec::new();
    let mut cubic_polys: Vec<CubicPoly> = Vec::new();
    for _j in 0..num_rounds {
      let mut eval_point_0 = Scalar::zero();
      let mut eval_point_2 = Scalar::zero();
      let mut eval_point_3 = Scalar::zero();

      let len = poly_A.len() / 2;
      for i in 0..len {
        // eval 0: bound_func is A(low)
        eval_point_0 = &eval_point_0 + comb_func(&poly_A[i], &poly_B[i], &poly_C[i]);

        // eval 2: bound_func is -A(low) + 2*A(high)
        let poly_A_bound_point = &poly_A[len + i] + &poly_A[len + i] - &poly_A[i];
        let poly_B_bound_point = &poly_B[len + i] + &poly_B[len + i] - &poly_B[i];
        let poly_C_bound_point = &poly_C[len + i] + &poly_C[len + i] - &poly_C[i];
        eval_point_2 = &eval_point_2
          + comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );

        // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
        let poly_A_bound_point = &poly_A_bound_point + &poly_A[len + i] - &poly_A[i];
        let poly_B_bound_point = &poly_B_bound_point + &poly_B[len + i] - &poly_B[i];
        let poly_C_bound_point = &poly_C_bound_point + &poly_C[len + i] - &poly_C[i];

        eval_point_3 = &eval_point_3
          + comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );
      }

      let poly = CubicPoly::new(eval_point_0, e - eval_point_0, eval_point_2, eval_point_3);

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");
      r.push(r_j);
      // bound all tables to the verifier's challenege
      poly_A.bound_poly_var_top(&r_j);
      poly_B.bound_poly_var_top(&r_j);
      poly_C.bound_poly_var_top(&r_j);
      e = poly.evaluate(&r_j);
      cubic_polys.push(poly);
    }

    (
      SumcheckInstanceProof::new(cubic_polys),
      r,
      vec![poly_A[0], poly_B[0], poly_C[0]],
    )
  }
}
