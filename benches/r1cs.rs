use std::time::Instant;

use libspartan::{
  parameters::POSEIDON_PARAMETERS_FR_377, poseidon_transcript::PoseidonTranscript, Instance,
  NIZKGens, NIZK,
};
use serde::Serialize;

#[derive(Default, Clone, Serialize)]
struct BenchmarkResults {
  power: usize,
  input_constraints: usize,
  spartan_verifier_circuit_constraints: usize,
  r1cs_instance_generation_time: u128,
  spartan_proving_time: u128,
  groth16_setup_time: u128,
  groth16_proving_time: u128,
  testudo_verification_time: u128,
  testudo_proving_time: u128,
}

fn main() {
  let mut writer = csv::Writer::from_path("testudo.csv").expect("unable to open csv writer");
  // for &s in [
  //   10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  // ]
  // .iter()
  // For testing purposes we currently bench on very small instance to ensure
  // correctness and then on biggest one for timings.
  for &s in [4, 26].iter() {
    println!("Running for {} inputs", s);
    let mut br = BenchmarkResults::default();
    let num_vars = (2_usize).pow(s as u32);
    let num_cons = num_vars;
    br.power = s;
    br.input_constraints = num_cons;
    let num_inputs = 10;

    let start = Instant::now();
    let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let duration = start.elapsed().as_millis();
    br.r1cs_instance_generation_time = duration;
    let mut prover_transcript = PoseidonTranscript::new(&POSEIDON_PARAMETERS_FR_377);

    let gens = NIZKGens::new(num_cons, num_vars, num_inputs);

    let start = Instant::now();
    let proof = NIZK::prove(&inst, vars, &inputs, &gens, &mut prover_transcript);
    let duration = start.elapsed().as_millis();
    br.spartan_proving_time = duration;

    let mut verifier_transcript = PoseidonTranscript::new(&POSEIDON_PARAMETERS_FR_377);
    let res = proof.verify(&inst, &inputs, &mut verifier_transcript, &gens);
    assert!(res.is_ok());
    br.spartan_verifier_circuit_constraints = res.unwrap();

    let mut verifier_transcript = PoseidonTranscript::new(&POSEIDON_PARAMETERS_FR_377);
    let res = proof.verify_groth16(&inst, &inputs, &mut verifier_transcript, &gens);
    assert!(res.is_ok());

    let (ds, dp, dv) = res.unwrap();
    br.groth16_setup_time = ds;
    br.groth16_proving_time = dp;

    br.testudo_proving_time = br.spartan_proving_time + br.groth16_proving_time;
    br.testudo_verification_time = dv;
    writer
      .serialize(br)
      .expect("unable to write results to csv");
    writer.flush().expect("wasn't able to flush");
  }
}
