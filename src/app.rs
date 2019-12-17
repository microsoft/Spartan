#![allow(non_snake_case)]
extern crate curve25519_dalek;
extern crate libspartan;
extern crate merlin;
extern crate rand;

use libspartan::dense_mlpoly::{DensePolynomial, PolyCommitmentBlinds, PolyCommitmentGens};
use libspartan::math::Math;
use libspartan::r1csinstance::{R1CSCommitmentGens, R1CSInstance};
use libspartan::scalar::Scalar;
use libspartan::spartan::{SpartanBlinds, SpartanGens, SpartanProof};
use merlin::Transcript;
use rand::rngs::OsRng;
use std::time::Instant;

pub fn main() {
  let num_vars = 1024 * 1024;
  let num_cons = num_vars;
  let num_inputs = 10;
  println!("Producing a synthetic R1CS");
  let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
  let n = inst.get_num_vars();
  let m = n.square_root();
  assert_eq!(n, m * m);
  println!("Finished producing a synthetic R1CS");

  let poly_vars = DensePolynomial::new(vars.clone());
  let poly_size = poly_vars.size();
  let r1cs_size = inst.size();

  let gens_z = PolyCommitmentGens::new(&poly_size, b"gens_z");
  let gens_r1cs = R1CSCommitmentGens::new(&r1cs_size, b"gens_r1cs");
  let mut csprng: OsRng = OsRng;
  // create a commitment to R1CSInstance
  println!("Encoding the R1CS relation");
  let start = Instant::now();
  let (comm, decomm) = SpartanProof::encode(&inst, &gens_r1cs);
  let duration = start.elapsed();
  println!("#### Encoder time is: {:?}", duration);

  // produce a proof of satisfiability
  let blinds_z = PolyCommitmentBlinds::new(&poly_size, &mut csprng);
  let gens = SpartanGens::new(gens_z, gens_r1cs);
  let blinds = SpartanBlinds::new(blinds_z, Scalar::one());

  let start = Instant::now();
  let mut prover_transcript = Transcript::new(b"example");
  let proof = SpartanProof::prove(
    &inst,
    &comm,
    &decomm,
    vars,
    &input,
    &blinds,
    &gens,
    &mut prover_transcript,
  );
  let duration = start.elapsed();
  println!("#### Prover time is: {:?}", duration);

  let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
  println!("#### Proof length is: {:?}", proof_encoded.len());

  let start = Instant::now();
  let mut verifier_transcript = Transcript::new(b"example");
  assert!(proof
    .verify(&comm, &input, &mut verifier_transcript, &gens)
    .is_ok());
  let duration = start.elapsed();
  println!("#### Verifier time is: {:?}", duration);
}
