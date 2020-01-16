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
use libspartan::nizk::DotProductProof;
use libspartan::scalar::Scalar;
use libspartan::scalar::ScalarBytes;
use rand::rngs::OsRng;

use criterion::*;

fn dotproduct_benchmark_dalek(c: &mut Criterion) {
  let mut csprng: OsRng = OsRng;

  for &s in [20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("dotproduct_benchmark_dalek");
    group.plot_config(plot_config);

    let n = (s as usize).pow2();
    let vec_a = (0..n)
      .map(|_i| ScalarBytes::random(&mut csprng))
      .collect::<Vec<ScalarBytes>>();
    let vec_b = (0..n)
      .map(|_i| ScalarBytes::random(&mut csprng))
      .collect::<Vec<ScalarBytes>>();

    let name = format!("dotproduct_dalek_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| compute_dotproduct(black_box(&vec_a), black_box(&vec_b)));
    });
    group.finish();
  }
}

fn compute_dotproduct(a: &Vec<ScalarBytes>, b: &Vec<ScalarBytes>) -> ScalarBytes {
  let mut res = ScalarBytes::zero();
  for i in 0..a.len() {
    res = &res + &a[i] * &b[i];
  }
  res
}

fn dotproduct_benchmark_opt(c: &mut Criterion) {
  let mut csprng: OsRng = OsRng;

  for &s in [20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("dotproduct_benchmark_opt");
    group.plot_config(plot_config);

    let n = (s as usize).pow2();
    let vec_a = (0..n)
      .map(|_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();
    let vec_b = (0..n)
      .map(|_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();

    let name = format!("dotproduct_opt_{}", n);
    group.bench_function(&name, move |b| {
      b.iter(|| DotProductProof::compute_dotproduct(black_box(&vec_a), black_box(&vec_b)));
    });
    group.finish();
  }
}

fn set_duration() -> Criterion {
  Criterion::default().sample_size(10)
  // .measurement_time(Duration::new(0, 50000000))
}

criterion_group! {
name = benches_dotproduct;
config = set_duration();
targets = dotproduct_benchmark_dalek, dotproduct_benchmark_opt
}

criterion_main!(benches_dotproduct);
