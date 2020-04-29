extern crate byteorder;
extern crate core;
extern crate criterion;
extern crate digest;
extern crate libspartan;
extern crate merlin;
extern crate rand;
extern crate sha3;

use libspartan::r1csinstance::R1CSInstance;
use libspartan::{NIZKGens, NIZK};
use merlin::Transcript;

use criterion::*;

fn nizk_prove_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("NIZK_prove_benchmark");
    group.plot_config(plot_config);

    let num_vars = (2 as usize).pow(s as u32);
    let num_cons = num_vars;
    let num_inputs = 10;

    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();

    let gens = NIZKGens::new(num_cons, num_vars);

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

    let num_vars = (2 as usize).pow(s as u32);
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();

    let gens = NIZKGens::new(num_cons, num_vars);

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
}

criterion_group! {
name = benches_nizk;
config = set_duration();
targets = nizk_prove_benchmark, nizk_verify_benchmark
}

criterion_main!(benches_nizk);
