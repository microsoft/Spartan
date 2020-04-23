#![allow(non_snake_case)]

extern crate byteorder;
extern crate core;
extern crate criterion;
extern crate curve25519_dalek;
extern crate digest;
extern crate libspartan;
extern crate merlin;
extern crate rand;
extern crate sha3;

use libspartan::commitments::MultiCommitGens;
use libspartan::dense_mlpoly::DensePolynomial;
use libspartan::math::Math;
use libspartan::nizk::DotProductProof;
use libspartan::scalar::Scalar;
use libspartan::sumcheck::ZKSumcheckInstanceProof;
use merlin::Transcript;
use rand::rngs::OsRng;

use criterion::*;

fn prove_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16, 20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("zksumcheck_prove_benchmark");
    group.plot_config(plot_config);

    // produce tables
    let gens_n = MultiCommitGens::new(3, b"test-m");
    let gens_1 = MultiCommitGens::new(1, b"test-1");
    let num_rounds = s;
    let n = s.pow2();

    let mut csprng: OsRng = OsRng;

    let vec_A = (0..n)
      .map(|_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    let vec_B = (0..n)
      .map(|_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    let claim = DotProductProof::compute_dotproduct(&vec_A, &vec_B);
    let mut poly_A = DensePolynomial::new(vec_A);
    let mut poly_B = DensePolynomial::new(vec_B);

    let blind_claim = Scalar::random(&mut csprng);
    let comb_func =
      |poly_A_comp: &Scalar, poly_B_comp: &Scalar| -> Scalar { poly_A_comp * poly_B_comp };

    let blinds = (
      (0..s)
        .map(|_i| Scalar::random(&mut csprng))
        .collect::<Vec<Scalar>>(),
      (0..s)
        .map(|_i| Scalar::random(&mut csprng))
        .collect::<Vec<Scalar>>(),
    );
    let name = format!("zksumcheck_prove_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut prover_transcript = Transcript::new(b"example");
        ZKSumcheckInstanceProof::prove_quad(
          black_box(&claim),
          black_box(&blind_claim),
          black_box(num_rounds),
          black_box(&mut poly_A),
          black_box(&mut poly_B),
          black_box(comb_func),
          black_box(&gens_1),
          black_box(&gens_n),
          black_box(&blinds),
          black_box(&mut prover_transcript),
        )
      });
    });
    group.finish();
  }
}

fn verify_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16, 20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("zksumcheck_verify_benchmark");
    group.plot_config(plot_config);

    // produce tables
    let gens_n = MultiCommitGens::new(3, b"test-m");
    let gens_1 = MultiCommitGens::new(1, b"test-1");
    let num_rounds = s;
    let n = s.pow2();

    let mut csprng: OsRng = OsRng;

    let vec_A = (0..n)
      .map(|_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    let vec_B = (0..n)
      .map(|_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    let claim = DotProductProof::compute_dotproduct(&vec_A, &vec_B);
    let mut poly_A = DensePolynomial::new(vec_A);
    let mut poly_B = DensePolynomial::new(vec_B);
    let blind_claim = Scalar::random(&mut csprng);
    let comb_func =
      |poly_A_comp: &Scalar, poly_B_comp: &Scalar| -> Scalar { poly_A_comp * poly_B_comp };

    let blinds = (
      (0..s)
        .map(|_i| Scalar::random(&mut csprng))
        .collect::<Vec<Scalar>>(),
      (0..s)
        .map(|_i| Scalar::random(&mut csprng))
        .collect::<Vec<Scalar>>(),
    );

    let mut prover_transcript = Transcript::new(b"example");
    let (proof, _r, _v, comm_claim) = ZKSumcheckInstanceProof::prove_quad(
      &claim,
      &blind_claim,
      num_rounds,
      &mut poly_A,
      &mut poly_B,
      comb_func,
      &gens_1,
      &gens_n,
      &blinds,
      &mut prover_transcript,
    );

    let name = format!("zksumcheck_verify_{}", n);
    let degree_bound = 2;
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut verifier_transcript = Transcript::new(b"example");
        assert!(proof
          .verify(
            black_box(&comm_claim),
            black_box(num_rounds),
            black_box(degree_bound),
            black_box(&gens_1),
            black_box(&gens_n),
            black_box(&mut verifier_transcript)
          )
          .is_ok())
      });
    });
    group.finish();
  }
}

fn set_duration() -> Criterion {
  Criterion::default().sample_size(10)
  // .measurement_time(Duration::new(0, 50000000))
}

criterion_group! {
name = benches_r1cs;
config = set_duration();
targets = verify_benchmark, prove_benchmark
}

criterion_main!(benches_r1cs);
