#![allow(non_snake_case)]
extern crate curve25519_dalek;
extern crate flate2;
extern crate libspartan;
extern crate merlin;
extern crate rand;

use flate2::{write::ZlibEncoder, Compression};
use libspartan::dense_mlpoly::{DensePolynomial, PolyCommitmentBlinds, PolyCommitmentGens};
use libspartan::r1csinstance::{R1CSCommitmentGens, R1CSInstance};
use libspartan::scalar::Scalar;
use libspartan::spartan::{SpartanBlinds, SpartanGens, SpartanProof};
use libspartan::timer::Timer;
use libspartan::math::Math;
use merlin::Transcript;
use rand::rngs::OsRng;

pub fn main() {
  for &s in [12, 16].iter() {
    let num_vars = (s as usize).pow2();
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    let poly_vars = DensePolynomial::new(vars.clone());
    let r1cs_size = inst.size();

    let gens_z = PolyCommitmentGens::new(poly_vars.get_num_vars(), b"gens_z");
    let gens_r1cs = R1CSCommitmentGens::new(&r1cs_size, b"gens_r1cs");
    let mut csprng: OsRng = OsRng;

    Timer::print(&format!("number_of_constraints {}", num_cons));
    // create a commitment to R1CSInstance
    let timer_encode = Timer::new("SpartanProof::encode");
    let (comm, decomm) = SpartanProof::encode(&inst, &gens_r1cs);
    timer_encode.stop();

    // produce a proof of satisfiability
    let blinds_z = PolyCommitmentBlinds::new(poly_vars.get_num_vars(), &mut csprng);
    let gens = SpartanGens::new(gens_z, gens_r1cs);
    let blinds = SpartanBlinds::new(blinds_z, Scalar::one());

    let timer_prove = Timer::new("SpartanProof::prove");
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
    timer_prove.stop();

    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &proof).unwrap();
    let proof_encoded = encoder.finish().unwrap();
    let msg_proof_len = format!("proof_compressed_len {:?}", proof_encoded.len());
    Timer::print(&msg_proof_len);

    let timer_verify = Timer::new("SpartanProof::verify");
    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&comm, &input, &mut verifier_transcript, &gens)
      .is_ok());
    timer_verify.stop();

    println!();
  }
}
