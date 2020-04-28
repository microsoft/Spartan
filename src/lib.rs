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

mod commitments;
mod dense_mlpoly;
mod errors;
mod group;
mod math;
mod nizk;
mod product_tree;
pub mod r1csinstance;
mod r1csproof;
mod random;
mod scalar;
mod sparse_mlpoly;
pub mod spartan;
mod sumcheck;
pub mod timer;
mod transcript;
mod unipoly;
