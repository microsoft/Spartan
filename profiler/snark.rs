#![allow(non_snake_case)]
extern crate flate2;
extern crate libspartan;
extern crate merlin;

use flate2::{write::ZlibEncoder, Compression};
use libspartan::{Instance, SNARKGens, SNARK};
use merlin::Transcript;

fn print(msg: &str) {
  let star = "* ";
  println!("{:indent$}{}{}", "", star, msg.to_string(), indent = 2);
}

pub fn main() {
  // the list of number of variables (and constraints) in an R1CS instance
  let inst_sizes = vec![10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];

  println!("Profiler:: SNARK");
  for &s in inst_sizes.iter() {
    let num_vars = (2 as usize).pow(s as u32);
    let num_cons = num_vars;
    let num_inputs = 10;

    // produce a synthetic R1CSInstance
    let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    // produce public generators
    let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_cons);

    // create a commitment to R1CSInstance
    let (comm, decomm) = SNARK::encode(&inst, &gens);

    // produce a proof of satisfiability
    let mut prover_transcript = Transcript::new(b"snark_example");
    let proof = SNARK::prove(&inst, &decomm, vars, &inputs, &gens, &mut prover_transcript);

    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &proof).unwrap();
    let proof_encoded = encoder.finish().unwrap();
    let msg_proof_len = format!("SNARK::proof_compressed_len {:?}", proof_encoded.len());
    print(&msg_proof_len);

    // verify the proof of satisfiability
    let mut verifier_transcript = Transcript::new(b"snark_example");
    assert!(proof
      .verify(&comm, &inputs, &mut verifier_transcript, &gens)
      .is_ok());

    println!();
  }
}
