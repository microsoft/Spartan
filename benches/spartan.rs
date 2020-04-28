extern crate byteorder;
extern crate core;
extern crate criterion;
extern crate digest;
extern crate libspartan;
extern crate merlin;
extern crate rand;
extern crate sha3;

use libspartan::math::Math;
use libspartan::r1csinstance::{R1CSCommitmentGens, R1CSInstance};
use libspartan::r1csproof::R1CSGens;
use libspartan::spartan::{NIZKGens, SNARKGens, NIZK, SNARK};
use merlin::Transcript;

use criterion::*;

fn snark_encode_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("SNARK_encode_benchmark");
    group.plot_config(plot_config);

    let num_vars = s.pow2();
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, _vars, _input) =
      R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();
    let r1cs_size = inst.size();
    let gens_r1cs = R1CSCommitmentGens::new(&r1cs_size, b"gens_r1cs");

    let name = format!("SNARK_encode_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        SNARK::encode(black_box(&inst), black_box(&gens_r1cs));
      });
    });
    group.finish();
  }
}

fn snark_prove_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("SNARK_prove_benchmark");
    group.plot_config(plot_config);

    let num_vars = s.pow2();
    let num_cons = num_vars;
    let num_inputs = 10;

    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();

    let r1cs_size = inst.size();
    let gens_r1cs_eval = R1CSCommitmentGens::new(&r1cs_size, b"gens_r1cs_eval");
    let gens_r1cs_sat = R1CSGens::new(num_cons, num_vars, b"gens_r1cs_sat");

    // produce a proof of satisfiability
    let (_comm, decomm) = SNARK::encode(&inst, &gens_r1cs_eval);
    let gens = SNARKGens::new(gens_r1cs_sat, gens_r1cs_eval);

    let name = format!("SNARK_prove_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut prover_transcript = Transcript::new(b"example");
        SNARK::prove(
          black_box(&inst),
          black_box(&decomm),
          black_box(vars.clone()),
          black_box(&input),
          black_box(&gens),
          black_box(&mut prover_transcript),
        );
      });
    });
    group.finish();
  }
}

fn snark_verify_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("SNARK_verify_benchmark");
    group.plot_config(plot_config);

    let num_vars = s.pow2();
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();

    let r1cs_size = inst.size();
    let gens_r1cs_eval = R1CSCommitmentGens::new(&r1cs_size, b"gens_r1cs_eval");

    // create a commitment to R1CSInstance
    let (comm, decomm) = SNARK::encode(&inst, &gens_r1cs_eval);

    let gens_r1cs_sat = R1CSGens::new(num_cons, num_vars, b"gens_r1cs_sat");
    let gens = SNARKGens::new(gens_r1cs_sat, gens_r1cs_eval);

    // produce a proof of satisfiability
    let mut prover_transcript = Transcript::new(b"example");
    let proof = SNARK::prove(&inst, &decomm, vars, &input, &gens, &mut prover_transcript);

    let name = format!("SNARK_verify_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut verifier_transcript = Transcript::new(b"example");
        assert!(proof
          .verify(
            black_box(&comm),
            black_box(&input),
            black_box(&mut verifier_transcript),
            black_box(&gens)
          )
          .is_ok());
      });
    });
    group.finish();
  }
}

fn nizk_prove_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("NIZK_prove_benchmark");
    group.plot_config(plot_config);

    let num_vars = s.pow2();
    let num_cons = num_vars;
    let num_inputs = 10;

    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();

    let gens_r1cs_sat = R1CSGens::new(num_cons, num_vars, b"gens_r1cs_sat");
    let gens = NIZKGens::new(gens_r1cs_sat);

    let name = format!("NIZK_prove_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut prover_transcript = Transcript::new(b"example");
        NIZK::prove(
          black_box(&inst),
          black_box(vars.clone()),
          black_box(&input),
          black_box(&gens),
          black_box(&mut prover_transcript),
        );
      });
    });
    group.finish();
  }
}

fn nizk_verify_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("NIZK_verify_benchmark");
    group.plot_config(plot_config);

    let num_vars = s.pow2();
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();

    let gens_r1cs_sat = R1CSGens::new(num_cons, num_vars, b"gens_r1cs_sat");
    let gens = NIZKGens::new(gens_r1cs_sat);

    // produce a proof of satisfiability
    let mut prover_transcript = Transcript::new(b"example");
    let proof = NIZK::prove(&inst, vars, &input, &gens, &mut prover_transcript);

    let name = format!("NIZK_verify_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut verifier_transcript = Transcript::new(b"example");
        assert!(proof
          .verify(
            black_box(&inst),
            black_box(&input),
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
name = benches_spartan;
config = set_duration();
targets = snark_encode_benchmark, snark_prove_benchmark, snark_verify_benchmark
}

criterion_main!(benches_spartan);
