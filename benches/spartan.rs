extern crate byteorder;
extern crate core;
extern crate criterion;
extern crate curve25519_dalek;
extern crate digest;
extern crate libspartan;
extern crate merlin;
extern crate rand;
extern crate sha3;

use libspartan::math::Math;
use libspartan::r1csinstance::{R1CSCommitmentGens, R1CSInstance};
use libspartan::r1csproof::{R1CSBlinds, R1CSGens};
use libspartan::scalar::Scalar;
use libspartan::spartan::{SpartanBlinds, SpartanGens, SpartanProof};
use merlin::Transcript;

use criterion::*;

fn encode_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("spartan_encode_benchmark");
    group.plot_config(plot_config);

    let num_vars = s.pow2();
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, _vars, _input) =
      R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();
    let m = n.square_root();
    assert_eq!(n, m * m);
    let r1cs_size = inst.size();
    let gens_r1cs = R1CSCommitmentGens::new(&r1cs_size, b"gens_r1cs");

    let name = format!("spartan_encode_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        SpartanProof::encode(black_box(&inst), black_box(&gens_r1cs));
      });
    });
    group.finish();
  }
}

fn prove_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("spartan_prove_benchmark");
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
    let blinds_r1cs_sat = R1CSBlinds::new(num_cons, num_vars);
    let blinds = SpartanBlinds::new(blinds_r1cs_sat, Scalar::one());

    let (_comm, decomm) = SpartanProof::encode(&inst, &gens_r1cs_eval);
    let gens = SpartanGens::new(gens_r1cs_sat, gens_r1cs_eval);

    let name = format!("spartan_prove_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut prover_transcript = Transcript::new(b"example");
        SpartanProof::prove(
          black_box(&inst),
          black_box(&decomm),
          black_box(vars.clone()),
          black_box(&input),
          black_box(&blinds),
          black_box(&gens),
          black_box(&mut prover_transcript),
        );
      });
    });
    group.finish();
  }
}

fn verify_benchmark(c: &mut Criterion) {
  for &s in [10, 12, 16].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("spartan_verify_benchmark");
    group.plot_config(plot_config);

    let num_vars = s.pow2();
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let n = inst.get_num_vars();

    let r1cs_size = inst.size();
    let gens_r1cs_eval = R1CSCommitmentGens::new(&r1cs_size, b"gens_r1cs_eval");

    // create a commitment to R1CSInstance
    let (comm, _decomm) = SpartanProof::encode(&inst, &gens_r1cs_eval);

    let gens_r1cs_sat = R1CSGens::new(num_cons, num_vars, b"gens_r1cs_sat");

    // produce a proof of satisfiability
    let blinds_r1cs_sat = R1CSBlinds::new(num_cons, num_vars);
    let blinds = SpartanBlinds::new(blinds_r1cs_sat, Scalar::one());

    let (_comm, decomm) = SpartanProof::encode(&inst, &gens_r1cs_eval);
    let gens = SpartanGens::new(gens_r1cs_sat, gens_r1cs_eval);

    let mut prover_transcript = Transcript::new(b"example");
    let proof = SpartanProof::prove(
      &inst,
      &decomm,
      vars,
      &input,
      &blinds,
      &gens,
      &mut prover_transcript,
    );

    let name = format!("spartan_verify_{}", n);
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

fn set_duration() -> Criterion {
  Criterion::default().sample_size(10)
  // .measurement_time(Duration::new(0, 50000000))
}

criterion_group! {
name = benches_spartan;
config = set_duration();
targets = encode_benchmark, prove_benchmark, verify_benchmark
}

criterion_main!(benches_spartan);
