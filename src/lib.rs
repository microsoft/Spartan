#![allow(non_snake_case)]
#![feature(test)]
extern crate byteorder;
extern crate core;
extern crate curve25519_dalek;
extern crate digest;
extern crate merlin;
extern crate rand;
extern crate rayon;
extern crate sha3;
extern crate test;

pub mod commitments;
pub mod dense_mlpoly;
mod errors;
pub mod math;
pub mod nizk;
pub mod r1csinstance;
pub mod r1csproof;
pub mod scalar;
mod scalar_25519;
pub mod sparse_mlpoly;
pub mod spartan;
mod sumcheck;
mod transcript;
mod unipoly;
