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
  DensePolynomial, EqPolynomial, PolyCommitmentBlinds, PolyCommitmentGens,
};
use libspartan::math::Math;
use libspartan::r1csinstance::R1CSInstance;
use libspartan::r1csproof::R1CSProof;
use merlin::Transcript;
use rand::rngs::OsRng;

use criterion::*;

fn prove_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16, 20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("r1cs_prove_benchmark");
    group.plot_config(plot_config);

    let num_vars = s.pow2();
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();
    let m = n.square_root();
    assert_eq!(n, m * m);

    let poly_vars = DensePolynomial::new(vars.clone());
    let poly_vars_size = poly_vars.size();

    let gens = PolyCommitmentGens::new(&poly_vars_size, b"test-m");
    let mut csprng: OsRng = OsRng;
    let blinds = PolyCommitmentBlinds::new(&poly_vars_size, &mut csprng);

    let name = format!("r1cs_prove_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut prover_transcript = Transcript::new(b"example");
        R1CSProof::prove(
          black_box(&inst),
          black_box(vars.clone()),
          black_box(&input),
          black_box(&blinds),
          black_box(&gens),
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
    let mut group = c.benchmark_group("r1cs_verify_benchmark");
    group.plot_config(plot_config);

    let num_vars = s.pow2();
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();
    let m = n.square_root();
    assert_eq!(n, m * m);

    let poly_vars = DensePolynomial::new(vars.clone());
    let poly_vars_size = poly_vars.size();

    let gens = PolyCommitmentGens::new(&poly_vars_size, b"test-m");
    let mut csprng: OsRng = OsRng;
    let blinds = PolyCommitmentBlinds::new(&poly_vars_size, &mut csprng);

    let mut prover_transcript = Transcript::new(b"example");
    let (proof, rx, ry) =
      R1CSProof::prove(&inst, vars, &input, &blinds, &gens, &mut prover_transcript);

    let eval_table_rx = EqPolynomial::new(rx.clone()).evals();
    let eval_table_ry = EqPolynomial::new(ry.clone()).evals();
    let inst_evals = inst.evaluate_with_tables(&eval_table_rx, &eval_table_ry);

    let name = format!("r1cs_verify_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut verifier_transcript = Transcript::new(b"example");
        assert!(proof
          .verify(
            black_box(num_vars),
            black_box(num_cons),
            black_box(&input),
            black_box(&inst_evals),
            black_box(&mut verifier_transcript),
            black_box(&gens)
          )
          .is_ok());
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
targets = prove_benchmark, verify_benchmark
}

criterion_main!(benches_r1cs);
