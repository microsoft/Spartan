# Spartan: High-speed zkSNARKs without trusted setup

![Rust](https://github.com/microsoft/Spartan/workflows/Rust/badge.svg)

Spartan is a high-speed zero-knowledge proof system, a cryptographic primitive that enables a prover to prove a mathematical statement to a verifier without revealing anything besides the validity of the statement. This repository provides `libspartan,` a Rust library that implements a zero-knowledge succinct non-interactive argument of knowledge (zkSNARK), which is a type of zero-knowledge proof system with short proofs and fast verification times. The details of the Spartan proof system are described in our [paper](https://eprint.iacr.org/2019/550) published at [CRYPTO 2020](https://crypto.iacr.org/2020/).

A simple example application is proving the knowledge of a secret s such that H(s) == d for a public d, where H is a cryptographic hash function (e.g., SHA-256, Keccak). A more complex application is a database-backed cloud service that produces proofs of correct state machine transitions for auditability. See this [paper](https://eprint.iacr.org/2020/758.pdf) for an overview and this [paper](https://eprint.iacr.org/2018/907.pdf) for details.

Note that this library has *not* received a security review or audit.

## Highlights
We now highlight Spartan's distinctive features.

* **No "toxic" waste:** Spartan is a *transparent* zkSNARK and does not require a trusted setup. So, it does not involve any trapdoors that must be kept secret or require a multi-party ceremony to produce public parameters.

* **General-purpose:** Spartan produces proofs for arbitrary NP statements. `libspartan` supports NP statements expressed as rank-1 constraint satisfiability (R1CS) instances, a popular language for which there exists efficient transformations and compiler toolchains from high-level programs of interest.

* **Sub-linear verification costs and linear-time proving costs:** Spartan is the first transparent proof system with sub-linear verification costs for arbitrary NP statements (e.g., R1CS). Spartan also features a time-optimal prover, a property that has remained elusive for nearly all zkSNARKs in the literature.

* **Standardized security:** Spartan's security relies on the hardness of computing discrete logarithms (a standard cryptographic assumption) in the random oracle model. `libspartan` uses `ristretto255`, a prime-order group abstraction atop `curve25519` (a high-speed elliptic curve). We use [`curve25519-dalek`](https://docs.rs/curve25519-dalek) for arithmetic over `ristretto255`. 

* **State-of-the-art performance:** 
Among transparent SNARKs, Spartan
offers the fastest prover with speedups of 36–152× depending on the baseline,
produces proofs that are shorter by 1.2–416×, and incurs the lowest verification
times with speedups of 3.6–1326×. When compared to the state-of-the-art zkSNARK
with trusted setup, Spartan’s prover is 2× faster for arbitrary R1CS instances and
16× faster for data-parallel workloads.

### Status
Development is ongoing (PRs are welcome!). For example, the library does not yet offer APIs to specify an NP statement, but we will in the future offer standardized APIs and also integrate with a compiler that produces R1CS instances from high level programs.

### Implementation details
`libspartan` uses [`merlin`](https://docs.rs/merlin/) to automate the Fiat-Shamir transform. We also introduce a new type called `RandomTape` that extends a `Transcript` in `merlin` to allow the prover's internal methods to produce private randomness using its private transcript without having to create `OsRng` objects throughout the code. An object of type `RandomTape` is initialized with a new random seed from `OsRng` for each proof produced by the library. 

## Examples
The following example shows how to use `libspartan` to create and verify a SNARK proof.
Some of our public APIs' style is inspired by the underlying crates we use.

```rust
# extern crate libspartan;
# extern crate merlin;
# use libspartan::{Instance, SNARKGens, SNARK};
# use merlin::Transcript;
# fn main() {
    // specify the size of an R1CS instance
    let num_vars = 1024;
    let num_cons = 1024;
    let num_inputs = 10;
    let num_non_zero_entries = 1024;

    // produce public parameters
    let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_non_zero_entries);

    // ask the library to produce a synthentic R1CS instance
    let (inst, vars, inputs) = Instance::new(num_cons, num_vars, num_inputs);

    // create a commitment to the R1CS instance
    let (comm, decomm) = SNARK::encode(&inst, &gens);

    // produce a proof of satisfiability
    let mut prover_transcript = Transcript::new(b"snark_example");
    let proof = SNARK::prove(&inst, &decomm, vars, &inputs, &gens, &mut prover_transcript);

    // verify the proof of satisfiability
    let mut verifier_transcript = Transcript::new(b"snark_example");
    assert!(proof
      .verify(&comm, &inputs, &mut verifier_transcript, &gens)
      .is_ok());
# }
```

Here is another example to use the NIZK variant of the Spartan proof system:
```rust
# extern crate libspartan;
# extern crate merlin;
# use libspartan::{Instance, NIZKGens, NIZK};
# use merlin::Transcript;
# fn main() {
    // specify the size of an R1CS instance
    let num_vars = 1024;
    let num_cons = 1024;
    let num_inputs = 10;

    // produce public parameters
    let gens = NIZKGens::new(num_cons, num_vars);

    // ask the library to produce a synthentic R1CS instance
    let (inst, vars, inputs) = Instance::new(num_cons, num_vars, num_inputs);

    // produce a proof of satisfiability
    let mut prover_transcript = Transcript::new(b"nizk_example");
    let proof = NIZK::prove(&inst, vars, &inputs, &gens, &mut prover_transcript);

    // verify the proof of satisfiability
    let mut verifier_transcript = Transcript::new(b"nizk_example");
    assert!(proof
      .verify(&inst, &inputs, &mut verifier_transcript, &gens)
      .is_ok());
# }
```

## Building `libspartan`
Install [`rustup`](https://rustup.rs/)

Switch to nightly Rust using `rustup`:
```text
rustup default nightly
```

Clone the repository:
```text
git clone https://github.com/Microsoft/Spartan
cd Spartan
```

To build docs for public APIs of `libspartan`:
```text
cargo doc
```

To run tests:
```text
RUSTFLAGS="-C target_cpu=native" cargo test
```

To build `libspartan`:
```text
RUSTFLAGS="-C target_cpu=native" cargo build --release
```

> NOTE: We enable SIMD instructions in `curve25519-dalek` by default, so if it fails to build remove the "simd_backend" feature argument in `Cargo.toml`.

### Supported features
* `profile`: enables fine-grained profiling information (see below for its use)

## Performance

### End-to-end benchmarks
`libspartan` includes two benches: `benches/nizk.rs` and `benches/snark.rs`. If you report the performance of Spartan in a research paper, we recommend using these benches for higher accuracy instead of fine-grained profiling (listed below).

To run end-to-end benchmarks:
```text 
RUSTFLAGS="-C target_cpu=native" cargo bench
```

### Fine-grained profiling
Build `libspartan` with `profile` feature enabled. It creates two profilers: `./target/release/snark` and `./target/release/nizk`.

These profilers report performance as depicted below (for varying R1CS instance sizes). The reported
performance is from running the profilers on a Microsoft Surface Laptop 3 on a single CPU core of Intel Core i7-1065G7 running Ubuntu 20.04 (atop WSL2 on Windows 10).
See Section 9 in our [paper](https://eprint.iacr.org/2019/550) to see how this compares with other zkSNARKs in the literature.

```text
$ ./target/release/snark 
Profiler:: SNARK
  * number_of_constraints 1048576
  * number_of_variables 1048576
  * number_of_inputs 10
  * number_non-zero_entries_A 1048576
  * number_non-zero_entries_B 1048576
  * number_non-zero_entries_C 1048576
  * SNARK::encode
  * SNARK::encode 14.2644201s
  * SNARK::prove
    * R1CSProof::prove
      * polycommit
      * polycommit 2.7175848s
      * prove_sc_phase_one
      * prove_sc_phase_one 683.7481ms
      * prove_sc_phase_two
      * prove_sc_phase_two 846.1056ms
      * polyeval
      * polyeval 193.4216ms
    * R1CSProof::prove 4.4416193s
    * len_r1cs_sat_proof 47024
    * eval_sparse_polys
    * eval_sparse_polys 377.357ms
    * R1CSEvalProof::prove
      * commit_nondet_witness
      * commit_nondet_witness 14.4507331s
      * build_layered_network
      * build_layered_network 3.4360521s
      * evalproof_layered_network
        * len_product_layer_proof 64712
      * evalproof_layered_network 15.5708066s
    * R1CSEvalProof::prove 34.2930559s
    * len_r1cs_eval_proof 133720
  * SNARK::prove 39.1297568s
  * SNARK::proof_compressed_len 141768
  * SNARK::verify
    * verify_sat_proof
    * verify_sat_proof 20.0828ms
    * verify_eval_proof
      * verify_polyeval_proof
        * verify_prod_proof
        * verify_prod_proof 1.1847ms
        * verify_hash_proof
        * verify_hash_proof 81.06ms
      * verify_polyeval_proof 82.3583ms
    * verify_eval_proof 82.8937ms
  * SNARK::verify 103.0536ms
```

```text
$ ./target/release/nizk 
Profiler:: NIZK
  * number_of_constraints 1048576
  * number_of_variables 1048576
  * number_of_inputs 10
  * number_non-zero_entries_A 1048576
  * number_non-zero_entries_B 1048576
  * number_non-zero_entries_C 1048576
  * NIZK::prove
    * R1CSProof::prove
      * polycommit
      * polycommit 2.7220635s
      * prove_sc_phase_one
      * prove_sc_phase_one 722.5487ms
      * prove_sc_phase_two
      * prove_sc_phase_two 862.6796ms
      * polyeval
      * polyeval 190.2233ms
    * R1CSProof::prove 4.4982305s
    * len_r1cs_sat_proof 47024
  * NIZK::prove 4.5139888s
  * NIZK::proof_compressed_len 48134
  * NIZK::verify
    * eval_sparse_polys
    * eval_sparse_polys 395.0847ms
    * verify_sat_proof
    * verify_sat_proof 19.286ms
  * NIZK::verify 414.5102ms
```

## LICENSE

See [LICENSE](./LICENSE)

## Contributing

See [CONTRIBUTING](./CONTRIBUTING.md)
