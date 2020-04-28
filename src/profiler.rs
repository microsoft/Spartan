#![allow(non_snake_case)]
extern crate flate2;
extern crate libspartan;
extern crate merlin;
extern crate rand;

use flate2::{write::ZlibEncoder, Compression};
use libspartan::math::Math;
use libspartan::r1csinstance::{R1CSCommitmentGens, R1CSInstance};
use libspartan::r1csproof::R1CSGens;
use libspartan::spartan::{NIZKGens, SNARKGens, NIZK, SNARK};
use libspartan::timer::Timer;
use merlin::Transcript;

pub fn main() {
  // the list of number of variables (and constraints) in an R1CS instance
  let inst_sizes = vec![12, 16, 20];

  println!("Profiler:: SNARK");
  for &s in inst_sizes.iter() {
    let num_vars = (s as usize).pow2();
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    Timer::print(&format!("number_of_constraints {}", num_cons));

    let r1cs_size = inst.size();
    let gens_r1cs_eval = R1CSCommitmentGens::new(&r1cs_size, b"gens_r1cs_eval");

    // create a commitment to R1CSInstance
    let timer_encode = Timer::new("SNARK::encode");
    let (comm, decomm) = SNARK::encode(&inst, &gens_r1cs_eval);
    timer_encode.stop();

    let gens_r1cs_sat = R1CSGens::new(num_cons, num_vars, b"gens_r1cs_sat");
    let gens = SNARKGens::new(gens_r1cs_sat, gens_r1cs_eval);

    // produce a proof of satisfiability
    let timer_prove = Timer::new("SNARK::prove");
    let mut prover_transcript = Transcript::new(b"example");
    let proof = SNARK::prove(&inst, &decomm, vars, &input, &gens, &mut prover_transcript);
    timer_prove.stop();

    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &proof).unwrap();
    let proof_encoded = encoder.finish().unwrap();
    let msg_proof_len = format!("SNARK::proof_compressed_len {:?}", proof_encoded.len());
    Timer::print(&msg_proof_len);

    // verify the proof of satisfiability
    let timer_verify = Timer::new("SNARK::verify");
    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&comm, &input, &mut verifier_transcript, &gens)
      .is_ok());
    timer_verify.stop();

    println!();
  }

  println!("Profiler:: NIZK");
  for &s in inst_sizes.iter() {
    let num_vars = (s as usize).pow2();
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    Timer::print(&format!("number_of_constraints {}", num_cons));

    let gens_r1cs_sat = R1CSGens::new(num_cons, num_vars, b"gens_r1cs_sat");
    let gens = NIZKGens::new(gens_r1cs_sat);

    // produce a proof of satisfiability
    let timer_prove = Timer::new("NIZK::prove");
    let mut prover_transcript = Transcript::new(b"example");
    let proof = NIZK::prove(&inst, vars, &input, &gens, &mut prover_transcript);
    timer_prove.stop();

    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &proof).unwrap();
    let proof_encoded = encoder.finish().unwrap();
    let msg_proof_len = format!("NIZK::proof_compressed_len {:?}", proof_encoded.len());
    Timer::print(&msg_proof_len);

    // verify the proof of satisfiability
    let timer_verify = Timer::new("NIZK::verify");
    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&inst, &input, &mut verifier_transcript, &gens)
      .is_ok());
    timer_verify.stop();

    println!();
  }
}
