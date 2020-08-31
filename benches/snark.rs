extern crate libspartan;
extern crate merlin;

use libspartan::{Instance, SNARKGens, SNARK};
use merlin::Transcript;

use criterion::*;

fn snark_encode_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("SNARK_encode_benchmark");
    group.plot_config(plot_config);

    let num_vars = (2 as usize).pow(s as u32);
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, _vars, _inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    // produce public parameters
    let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_cons);

    // produce a commitment to R1CS instance
    let name = format!("SNARK_encode_{}", num_cons);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        SNARK::encode(black_box(&inst), black_box(&gens));
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

    let num_vars = (2 as usize).pow(s as u32);
    let num_cons = num_vars;
    let num_inputs = 10;

    let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    // produce public parameters
    let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_cons);

    // produce a commitment to R1CS instance
    let (_comm, decomm) = SNARK::encode(&inst, &gens);

    // produce a proof
    let name = format!("SNARK_prove_{}", num_cons);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut prover_transcript = Transcript::new(b"example");
        SNARK::prove(
          black_box(&inst),
          black_box(&decomm),
          black_box(vars.clone()),
          black_box(&inputs),
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

    let num_vars = (2 as usize).pow(s as u32);
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    // produce public parameters
    let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_cons);

    // produce a commitment to R1CS instance
    let (comm, decomm) = SNARK::encode(&inst, &gens);

    // produce a proof of satisfiability
    let mut prover_transcript = Transcript::new(b"example");
    let proof = SNARK::prove(&inst, &decomm, vars, &inputs, &gens, &mut prover_transcript);

    // verify the proof
    let name = format!("SNARK_verify_{}", num_cons);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut verifier_transcript = Transcript::new(b"example");
        assert!(proof
          .verify(
            black_box(&comm),
            black_box(&inputs),
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
name = benches_snark;
config = set_duration();
targets = snark_encode_benchmark, snark_prove_benchmark, snark_verify_benchmark
}

criterion_main!(benches_snark);
