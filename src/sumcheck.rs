use super::dense_mlpoly::DensePolynomial;
use super::errors::ProofVerifyError;
use super::scalar::Scalar;
use super::transcript::{AppendToTranscript, ProofTranscript};
use super::unipoly::{CompressedUniPoly, UniPoly};
use itertools::izip;
use merlin::Transcript;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct SumcheckInstanceProof {
  compressed_polys: Vec<CompressedUniPoly>,
}

impl SumcheckInstanceProof {
  pub fn new(compressed_polys: Vec<CompressedUniPoly>) -> SumcheckInstanceProof {
    SumcheckInstanceProof { compressed_polys }
  }

  pub fn verify(
    &self,
    claim: Scalar,
    num_rounds: usize,
    degree_bound: usize,
    transcript: &mut Transcript,
  ) -> Result<(Scalar, Vec<Scalar>), ProofVerifyError> {
    let mut e = claim;
    let mut r: Vec<Scalar> = Vec::new();

    // verify that there is a univariate polynomial for each round
    assert_eq!(self.compressed_polys.len(), num_rounds);
    for i in 0..self.compressed_polys.len() {
      let poly = self.compressed_polys[i].decompress(&e);

      // verify degree bound
      assert_eq!(poly.degree(), degree_bound);

      // check if G_k(0) + G_k(1) = e
      assert_eq!(poly.eval_at_zero() + poly.eval_at_one(), e);

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
impl SumcheckInstanceProof {
  pub fn prove_quad<F>(
    claim: &Scalar,
    num_rounds: usize,
    poly_A: &mut DensePolynomial,
    poly_B: &mut DensePolynomial,
    comb_func: F,
    transcript: &mut Transcript,
  ) -> (Self, Vec<Scalar>, Vec<Scalar>)
  where
    F: Fn(&Scalar, &Scalar) -> Scalar,
  {
    let mut e = *claim;
    let mut r: Vec<Scalar> = Vec::new();
    let mut quad_polys: Vec<CompressedUniPoly> = Vec::new();
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

      let evals = vec![eval_point_0, e - eval_point_0, eval_point_2];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");
      r.push(r_j);
      // bound all tables to the verifier's challenege
      poly_A.bound_poly_var_top(&r_j);
      poly_B.bound_poly_var_top(&r_j);

      e = poly.evaluate(&r_j);
      quad_polys.push(poly.compress());
    }

    (
      SumcheckInstanceProof::new(quad_polys),
      r,
      vec![poly_A[0], poly_B[0]],
    )
  }

  pub fn prove_cubic<F>(
    claim: &Scalar,
    num_rounds: usize,
    poly_A: &mut DensePolynomial,
    poly_B: &mut DensePolynomial,
    poly_C: &mut DensePolynomial,
    comb_func: F,
    transcript: &mut Transcript,
  ) -> (Self, Vec<Scalar>, Vec<Scalar>)
  where
    F: Fn(&Scalar, &Scalar, &Scalar) -> Scalar,
  {
    let mut e = *claim;
    let mut r: Vec<Scalar> = Vec::new();
    let mut cubic_polys: Vec<CompressedUniPoly> = Vec::new();
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

      let evals = vec![eval_point_0, e - eval_point_0, eval_point_2, eval_point_3];
      let poly = UniPoly::from_evals(&evals);

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
      cubic_polys.push(poly.compress());
    }

    (
      SumcheckInstanceProof::new(cubic_polys),
      r,
      vec![poly_A[0], poly_B[0], poly_C[0]],
    )
  }

  pub fn prove_cubic_with_additive_term<F>(
    claim: &Scalar,
    num_rounds: usize,
    poly_A: &mut DensePolynomial,
    poly_B: &mut DensePolynomial,
    poly_C: &mut DensePolynomial,
    poly_D: &mut DensePolynomial,
    comb_func: F,
    transcript: &mut Transcript,
  ) -> (Self, Vec<Scalar>, Vec<Scalar>)
  where
    F: Fn(&Scalar, &Scalar, &Scalar, &Scalar) -> Scalar,
  {
    let mut e = *claim;
    let mut r: Vec<Scalar> = Vec::new();
    let mut cubic_polys: Vec<CompressedUniPoly> = Vec::new();
    for _j in 0..num_rounds {
      let mut eval_point_0 = Scalar::zero();
      let mut eval_point_2 = Scalar::zero();
      let mut eval_point_3 = Scalar::zero();

      let len = poly_A.len() / 2;
      for i in 0..len {
        // eval 0: bound_func is A(low)
        eval_point_0 = &eval_point_0 + comb_func(&poly_A[i], &poly_B[i], &poly_C[i], &poly_D[i]);

        // eval 2: bound_func is -A(low) + 2*A(high)
        let poly_A_bound_point = &poly_A[len + i] + &poly_A[len + i] - &poly_A[i];
        let poly_B_bound_point = &poly_B[len + i] + &poly_B[len + i] - &poly_B[i];
        let poly_C_bound_point = &poly_C[len + i] + &poly_C[len + i] - &poly_C[i];
        let poly_D_bound_point = &poly_D[len + i] + &poly_D[len + i] - &poly_D[i];
        eval_point_2 = &eval_point_2
          + comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
            &poly_D_bound_point,
          );

        // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
        let poly_A_bound_point = &poly_A_bound_point + &poly_A[len + i] - &poly_A[i];
        let poly_B_bound_point = &poly_B_bound_point + &poly_B[len + i] - &poly_B[i];
        let poly_C_bound_point = &poly_C_bound_point + &poly_C[len + i] - &poly_C[i];
        let poly_D_bound_point = &poly_D_bound_point + &poly_D[len + i] - &poly_D[i];
        eval_point_3 = &eval_point_3
          + comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
            &poly_D_bound_point,
          );
      }

      let evals = vec![eval_point_0, e - eval_point_0, eval_point_2, eval_point_3];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");
      r.push(r_j);
      // bound all tables to the verifier's challenege
      poly_A.bound_poly_var_top(&r_j);
      poly_B.bound_poly_var_top(&r_j);
      poly_C.bound_poly_var_top(&r_j);
      poly_D.bound_poly_var_top(&r_j);
      e = poly.evaluate(&r_j);
      cubic_polys.push(poly.compress());
    }

    (
      SumcheckInstanceProof::new(cubic_polys),
      r,
      vec![poly_A[0], poly_B[0], poly_C[0], poly_D[0]],
    )
  }

  pub fn prove_cubic_batched<F>(
    claim: &Scalar,
    num_rounds: usize,
    poly_vec_par: (
      &mut Vec<&mut DensePolynomial>,
      &mut Vec<&mut DensePolynomial>,
      &mut DensePolynomial,
    ),
    poly_vec_seq: (
      &mut Vec<&mut DensePolynomial>,
      &mut Vec<&mut DensePolynomial>,
      &mut Vec<&mut DensePolynomial>,
    ),
    coeffs: &[Scalar],
    comb_func: F,
    transcript: &mut Transcript,
  ) -> (
    Self,
    Vec<Scalar>,
    (Vec<Scalar>, Vec<Scalar>, Scalar),
    (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>),
  )
  where
    F: Fn(&Scalar, &Scalar, &Scalar) -> Scalar,
  {
    let (poly_A_vec_par, poly_B_vec_par, poly_C_par) = poly_vec_par;
    let (poly_A_vec_seq, poly_B_vec_seq, poly_C_vec_seq) = poly_vec_seq;

    //let (poly_A_vec_seq, poly_B_vec_seq, poly_C_vec_seq) = poly_vec_seq;
    let mut e = *claim;
    let mut r: Vec<Scalar> = Vec::new();
    let mut cubic_polys: Vec<CompressedUniPoly> = Vec::new();

    for _j in 0..num_rounds {
      let mut evals: Vec<(Scalar, Scalar, Scalar)> = Vec::new();

      for (poly_A, poly_B) in poly_A_vec_par.iter().zip(poly_B_vec_par.iter()) {
        let mut eval_point_0 = Scalar::zero();
        let mut eval_point_2 = Scalar::zero();
        let mut eval_point_3 = Scalar::zero();

        let len = poly_A.len() / 2;
        for i in 0..len {
          // eval 0: bound_func is A(low)
          eval_point_0 = &eval_point_0 + comb_func(&poly_A[i], &poly_B[i], &poly_C_par[i]);

          // eval 2: bound_func is -A(low) + 2*A(high)
          let poly_A_bound_point = &poly_A[len + i] + &poly_A[len + i] - &poly_A[i];
          let poly_B_bound_point = &poly_B[len + i] + &poly_B[len + i] - &poly_B[i];
          let poly_C_bound_point = &poly_C_par[len + i] + &poly_C_par[len + i] - &poly_C_par[i];
          eval_point_2 = &eval_point_2
            + comb_func(
              &poly_A_bound_point,
              &poly_B_bound_point,
              &poly_C_bound_point,
            );

          // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
          let poly_A_bound_point = &poly_A_bound_point + &poly_A[len + i] - &poly_A[i];
          let poly_B_bound_point = &poly_B_bound_point + &poly_B[len + i] - &poly_B[i];
          let poly_C_bound_point = &poly_C_bound_point + &poly_C_par[len + i] - &poly_C_par[i];

          eval_point_3 = &eval_point_3
            + comb_func(
              &poly_A_bound_point,
              &poly_B_bound_point,
              &poly_C_bound_point,
            );
        }

        evals.push((eval_point_0, eval_point_2, eval_point_3));
      }

      for (poly_A, poly_B, poly_C) in izip!(
        poly_A_vec_seq.iter(),
        poly_B_vec_seq.iter(),
        poly_C_vec_seq.iter()
      ) {
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
        evals.push((eval_point_0, eval_point_2, eval_point_3));
      }

      let evals_combined_0 = (0..evals.len()).map(|i| evals[i].0 * coeffs[i]).sum();
      let evals_combined_2 = (0..evals.len()).map(|i| evals[i].1 * coeffs[i]).sum();
      let evals_combined_3 = (0..evals.len()).map(|i| evals[i].2 * coeffs[i]).sum();

      let evals = vec![
        evals_combined_0,
        e - evals_combined_0,
        evals_combined_2,
        evals_combined_3,
      ];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      poly.append_to_transcript(b"poly", transcript);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"challenge_nextround");
      r.push(r_j);

      // bound all tables to the verifier's challenege
      for (poly_A, poly_B) in poly_A_vec_par.iter_mut().zip(poly_B_vec_par.iter_mut()) {
        poly_A.bound_poly_var_top(&r_j);
        poly_B.bound_poly_var_top(&r_j);
      }
      poly_C_par.bound_poly_var_top(&r_j);

      for (poly_A, poly_B, poly_C) in izip!(
        poly_A_vec_seq.iter_mut(),
        poly_B_vec_seq.iter_mut(),
        poly_C_vec_seq.iter_mut()
      ) {
        poly_A.bound_poly_var_top(&r_j);
        poly_B.bound_poly_var_top(&r_j);
        poly_C.bound_poly_var_top(&r_j);
      }

      e = poly.evaluate(&r_j);
      cubic_polys.push(poly.compress());
    }

    let poly_A_par_final = (0..poly_A_vec_par.len())
      .map(|i| poly_A_vec_par[i][0])
      .collect();
    let poly_B_par_final = (0..poly_B_vec_par.len())
      .map(|i| poly_B_vec_par[i][0])
      .collect();
    let claims_prod = (poly_A_par_final, poly_B_par_final, poly_C_par[0]);

    let poly_A_seq_final = (0..poly_A_vec_seq.len())
      .map(|i| poly_A_vec_seq[i][0])
      .collect();
    let poly_B_seq_final = (0..poly_B_vec_seq.len())
      .map(|i| poly_B_vec_seq[i][0])
      .collect();
    let poly_C_seq_final = (0..poly_C_vec_seq.len())
      .map(|i| poly_C_vec_seq[i][0])
      .collect();
    let claims_dotp = (poly_A_seq_final, poly_B_seq_final, poly_C_seq_final);

    (
      SumcheckInstanceProof::new(cubic_polys),
      r,
      claims_prod,
      claims_dotp,
    )
  }
}
