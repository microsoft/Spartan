extern crate byteorder;
extern crate core;
extern crate criterion;
extern crate curve25519_dalek;
extern crate digest;
extern crate libspartan;
extern crate merlin;
extern crate rand;
extern crate sha3;

use libspartan::dense_mlpoly::{
  DensePolynomial, PolyCommitmentBlinds, PolyCommitmentGens, PolyEvalProof,
};
use libspartan::math::Math;
use libspartan::scalar::Scalar;
use merlin::Transcript;
use rand::rngs::OsRng;

use criterion::*;

fn commit_benchmark(c: &mut Criterion) {
  let mut csprng: OsRng = OsRng;

  for &s in [4, 8, 12, 14, 16, 20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("commit_benchmark");
    group.plot_config(plot_config);

    let n = (s as usize).pow2();
    let m = n.square_root();
    let z = (0..n)
      .map(|_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    assert_eq!(m * m, z.len()); // check if Z's size if a perfect square

    let poly = DensePolynomial::new(z);
    let gens = PolyCommitmentGens::new(&poly.size(), b"test-m");
    let blinds = PolyCommitmentBlinds::new(&poly.size(), &mut csprng);
    let name = format!("polycommit_commit_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| poly.commit(black_box(&blinds), black_box(&gens)));
    });
    group.finish();
  }
}

fn eval_benchmark(c: &mut Criterion) {
  let mut csprng: OsRng = OsRng;

  for &s in [4, 8, 12, 14, 16, 20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("eval_benchmark");
    group.plot_config(plot_config);

    let n = (s as usize).pow2();
    let m = n.square_root();
    let mut z: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      z.push(Scalar::random(&mut csprng));
    }
    assert_eq!(m * m, z.len()); // check if Z's size if a perfect square

    let poly = DensePolynomial::new(z);

    let mut r: Vec<Scalar> = Vec::new();
    for _ in 0..s {
      r.push(Scalar::random(&mut csprng));
    }

    let name = format!("polycommit_eval_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| poly.evaluate(black_box(&r)));
    });
    group.finish();
  }
}

fn evalproof_benchmark(c: &mut Criterion) {
  let mut csprng: OsRng = OsRng;

  for &s in [4, 8, 12, 14, 16, 20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("evalproof_benchmark");
    group.plot_config(plot_config);

    let n = (s as usize).pow2();
    let m = n.square_root();
    let mut z: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      z.push(Scalar::random(&mut csprng));
    }
    assert_eq!(m * m, z.len()); // check if Z's size if a perfect square

    let poly = DensePolynomial::new(z);

    let gens = PolyCommitmentGens::new(&poly.size(), b"test-m");
    let blinds = PolyCommitmentBlinds::new(&poly.size(), &mut csprng);

    let mut r: Vec<Scalar> = Vec::new();
    for _ in 0..s {
      r.push(Scalar::random(&mut csprng));
    }

    let poly_commitment = poly.commit(&blinds, &gens);
    let eval = poly.evaluate(&r);

    let name = format!("polycommit_evalproof_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut prover_transcript = Transcript::new(b"example");
        PolyEvalProof::prove(
          black_box(&poly),
          black_box(&poly_commitment),
          black_box(&blinds),
          black_box(&r),
          black_box(eval),
          black_box(&gens),
          black_box(&mut prover_transcript),
        )
      });
    });
    group.finish();
  }
}

fn evalproofverify_benchmark(c: &mut Criterion) {
  let mut csprng: OsRng = OsRng;

  for &s in [4, 8, 12, 14, 16, 20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("evalproofverify_benchmark");
    group.plot_config(plot_config);

    let n = s.pow2();
    let m = n.square_root();
    let mut z: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      z.push(Scalar::random(&mut csprng));
    }
    assert_eq!(m * m, z.len()); // check if Z's size if a perfect square

    let poly = DensePolynomial::new(z);
    let gens = PolyCommitmentGens::new(&poly.size(), b"test-m");
    let blinds = PolyCommitmentBlinds::new(&poly.size(), &mut csprng);

    let mut r: Vec<Scalar> = Vec::new();
    for _ in 0..s {
      r.push(Scalar::random(&mut csprng));
    }

    let poly_commitment = poly.commit(&blinds, &gens);
    let eval = poly.evaluate(&r);

    let mut prover_transcript = Transcript::new(b"example");
    let (proof, c_zr) = PolyEvalProof::prove(
      black_box(&poly),
      black_box(&poly_commitment),
      black_box(&blinds),
      black_box(&r),
      black_box(eval),
      black_box(&gens),
      black_box(&mut prover_transcript),
    );
    let name = format!("polycommit_evalproofverify_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut verifier_transcript = Transcript::new(b"example");

        proof.verify(
          black_box(&gens),
          black_box(&mut verifier_transcript),
          black_box(&r),
          black_box(c_zr),
          black_box(&poly_commitment),
        )
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
name = benches_polycommit;
config = set_duration();
targets = commit_benchmark, eval_benchmark, evalproof_benchmark, evalproofverify_benchmark
}

criterion_main!(benches_polycommit);
