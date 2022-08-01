extern crate byteorder;
extern crate core;
extern crate criterion;
extern crate digest;
extern crate libspartan;
extern crate merlin;
extern crate sha3;

use std::time::{Duration, SystemTime};

use libspartan::{
  parameters::POSEIDON_PARAMETERS_FR_377, poseidon_transcript::PoseidonTranscript, Instance, NIZK,
};

use criterion::*;

fn nizk_prove_benchmark(c: &mut Criterion) {
  for &s in [24, 28, 30].iter() {
    let mut group = c.benchmark_group("R1CS_prove_benchmark");

    let num_vars = (2_usize).pow(s as u32);
    let num_cons = num_vars;
    let num_inputs = 10;
    let start = SystemTime::now();
    let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let end = SystemTime::now();
    let duration = end.duration_since(start).unwrap();
    println!(
      "Generating r1cs instance with {} constraints took {} ms",
      num_cons,
      duration.as_millis()
    );

    let name = format!("R1CS_prove_{}", num_vars);
    group
      .measurement_time(Duration::from_secs(60))
      .bench_function(&name, move |b| {
        b.iter(|| {
          let mut prover_transcript = PoseidonTranscript::new(&POSEIDON_PARAMETERS_FR_377);
          NIZK::prove(
            black_box(&inst),
            black_box(vars.clone()),
            black_box(&inputs),
            black_box(&mut prover_transcript),
          );
        });
      });
    group.finish();
  }
}

fn nizk_verify_benchmark(c: &mut Criterion) {
  for &s in [4, 6, 8, 10, 12, 16, 20, 24, 28, 30].iter() {
    let mut group = c.benchmark_group("R1CS_verify_benchmark");

    let num_vars = (2_usize).pow(s as u32);
    let num_cons = num_vars;
    // these are the public io
    let num_inputs = 10;
    let start = SystemTime::now();
    let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let end = SystemTime::now();
    let duration = end.duration_since(start).unwrap();
    println!(
      "Generating r1cs instance with {} constraints took {} ms",
      num_cons,
      duration.as_millis()
    );
    // produce a proof of satisfiability
    let mut prover_transcript = PoseidonTranscript::new(&POSEIDON_PARAMETERS_FR_377);
    let proof = NIZK::prove(&inst, vars, &inputs, &mut prover_transcript);

    let name = format!("R1CS_verify_{}", num_cons);
    group
      .measurement_time(Duration::from_secs(60))
      .bench_function(&name, move |b| {
        b.iter(|| {
          let mut verifier_transcript = PoseidonTranscript::new(&POSEIDON_PARAMETERS_FR_377);
          assert!(proof
            .verify(
              black_box(&inst),
              black_box(&inputs),
              black_box(&mut verifier_transcript),
            )
            .is_ok());
        });
      });
    group.finish();
  }
}

fn nizk_verify_groth16_benchmark(c: &mut Criterion) {
  for &s in [4, 6, 8, 10, 12, 16, 20, 24, 28, 30].iter() {
    let mut group = c.benchmark_group("R1CS_verify_groth16_benchmark");

    let num_vars = (2_usize).pow(s as u32);
    let num_cons = num_vars;
    // these are the public io
    let num_inputs = 10;
    let start = SystemTime::now();
    let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let end = SystemTime::now();
    let duration = end.duration_since(start).unwrap();
    println!(
      "Generating r1cs instance with {} constraints took {} ms",
      num_cons,
      duration.as_millis()
    );
    // produce a proof of satisfiability
    let mut prover_transcript = PoseidonTranscript::new(&POSEIDON_PARAMETERS_FR_377);
    let proof = NIZK::prove(&inst, vars, &inputs, &mut prover_transcript);

    let name = format!("R1CS_verify_groth16_{}", num_cons);
    group
      .measurement_time(Duration::from_secs(60))
      .bench_function(&name, move |b| {
        b.iter(|| {
          let mut verifier_transcript = PoseidonTranscript::new(&POSEIDON_PARAMETERS_FR_377);
          assert!(proof
            .verify_groth16(
              black_box(&inst),
              black_box(&inputs),
              black_box(&mut verifier_transcript),
            )
            .is_ok());
        });
      });
    group.finish();
  }
}

fn set_duration() -> Criterion {
  Criterion::default().sample_size(2)
}

criterion_group! {
name = benches_nizk;
config = set_duration();
targets =   nizk_prove_benchmark, nizk_verify_benchmark, nizk_verify_groth16_benchmark
}

criterion_main!(benches_nizk);
