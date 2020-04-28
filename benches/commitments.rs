extern crate byteorder;
extern crate core;
extern crate criterion;
extern crate digest;
extern crate libspartan;
extern crate merlin;
extern crate rand;
extern crate sha3;

use libspartan::commitments::{Commitments, MultiCommitGens};
use libspartan::math::Math;
use libspartan::scalar::Scalar;
use rand::rngs::OsRng;

use criterion::*;

fn commitment_benchmark(c: &mut Criterion) {
  let mut rng = OsRng;
  for &s in [20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("commitment_bools");
    group.plot_config(plot_config);

    let n = (s as usize).pow2();
    let gens = MultiCommitGens::new(n, b"test-m");
    let blind = Scalar::random(&mut rng);
    let vec: Vec<bool> = vec![true; n];
    let name = format!("commitment_bools_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| vec.commit(black_box(&blind), black_box(&gens)));
    });
    group.finish();
  }
}

fn set_duration() -> Criterion {
  Criterion::default().sample_size(10)
  // .measurement_time(Duration::new(0, 50000000))
}

criterion_group! {
name = benches_commitment;
config = set_duration();
targets = commitment_benchmark
}

criterion_main!(benches_commitment);
