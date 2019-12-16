# Spartan: High-speed zkSNARKs without trusted setup

Spartan is a research project to design high-speed zero-knowledge proof systems, a cryptographic protocol that enables a prover to prove a mathematical statement (e.g., that a given program was executed correctly) without revealing anything besides the validity of the statement. 

The current repository includes a library that implements 
a zero-knowledge succinct non-interactive arguments of knowledge (zkSNARKs), a type of zero-knowledge proof system with short proofs and verification times. Unlike many other zkSNARKs, Spartan does not require a trusted setup and its security relies on the hardness of computing discrete logarithms (a well-studied assumption). The scheme is described in our [paper](https://eprint.iacr.org/2019/550).

## Building libspartan
    cargo build
    # On a machine that supports avx2 or ifma instructions:
    export RUSTFLAGS="-C target_cpu=native" 
    cargo build --features "simd_backend" --release

## Performance
    cargo bench
    # On a machine that supports avx2 or ifma instructions:
    export RUSTFLAGS="-C target_cpu=native" 
    cargo bench --features "simd_backend"


## LICENSE

See [LICENSE](./LICENSE)

## Contributing

See [CONTRIBUTING](./CONTRIBUTING.md)
