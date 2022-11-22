use std::{borrow::Borrow, vec};

use super::scalar::Scalar;
use crate::{
  group::Fq,
  math::Math,
  sparse_mlpoly::{SparsePolyEntry, SparsePolynomial},
  unipoly::UniPoly,
};
use ark_bls12_377::{constraints::PairingVar as IV, Bls12_377 as I, Fr};
use ark_crypto_primitives::{
  snark::BooleanInputVar, CircuitSpecificSetupSNARK, SNARKGadget, SNARK,
};

use ark_ff::{BitIteratorLE, PrimeField, Zero};
use ark_groth16::{
  constraints::{Groth16VerifierGadget, PreparedVerifyingKeyVar, ProofVar},
  Groth16, PreparedVerifyingKey, Proof as GrothProof,
};

use ark_poly_commit::multilinear_pc::{
  data_structures::{Commitment, Proof, VerifierKey},
  MultilinearPC,
};
use ark_r1cs_std::{
  alloc::{AllocVar, AllocationMode},
  fields::fp::FpVar,
  prelude::{Boolean, EqGadget, FieldVar},
  R1CSVar,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_sponge::{
  constraints::CryptographicSpongeVar,
  poseidon::{constraints::PoseidonSpongeVar, PoseidonParameters},
};
use rand::{CryptoRng, Rng};

pub struct PoseidonTranscripVar {
  pub cs: ConstraintSystemRef<Fr>,
  pub sponge: PoseidonSpongeVar<Fr>,
  pub params: PoseidonParameters<Fr>,
}

impl PoseidonTranscripVar {
  fn new(
    cs: ConstraintSystemRef<Fr>,
    params: &PoseidonParameters<Fr>,
    challenge: Option<Fr>,
  ) -> Self {
    let mut sponge = PoseidonSpongeVar::new(cs.clone(), params);

    if let Some(c) = challenge {
      let c_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(c)).unwrap();
      sponge.absorb(&c_var).unwrap();
    }

    Self {
      cs,
      sponge,
      params: params.clone(),
    }
  }

  fn append(&mut self, input: &FpVar<Fr>) -> Result<(), SynthesisError> {
    self.sponge.absorb(&input)
  }

  fn append_vector(&mut self, input_vec: &[FpVar<Fr>]) -> Result<(), SynthesisError> {
    for input in input_vec.iter() {
      self.append(input)?;
    }
    Ok(())
  }

  fn challenge(&mut self) -> Result<FpVar<Fr>, SynthesisError> {
    let c_var = self.sponge.squeeze_field_elements(1).unwrap().remove(0);

    Ok(c_var)
  }

  fn challenge_vector(&mut self, len: usize) -> Result<Vec<FpVar<Fr>>, SynthesisError> {
    let c_vars = self.sponge.squeeze_field_elements(len).unwrap();

    Ok(c_vars)
  }
}

#[derive(Clone)]
pub struct UniPolyVar {
  pub coeffs: Vec<FpVar<Fr>>,
}

impl AllocVar<UniPoly, Fr> for UniPolyVar {
  fn new_variable<T: Borrow<UniPoly>>(
    cs: impl Into<Namespace<Fr>>,
    f: impl FnOnce() -> Result<T, SynthesisError>,
    mode: AllocationMode,
  ) -> Result<Self, SynthesisError> {
    f().and_then(|c| {
      let cs = cs.into();
      let cp: &UniPoly = c.borrow();
      let mut coeffs_var = Vec::new();
      for coeff in cp.coeffs.iter() {
        let coeff_var = FpVar::<Fr>::new_variable(cs.clone(), || Ok(coeff), mode)?;
        coeffs_var.push(coeff_var);
      }
      Ok(Self { coeffs: coeffs_var })
    })
  }
}

impl UniPolyVar {
  pub fn eval_at_zero(&self) -> FpVar<Fr> {
    self.coeffs[0].clone()
  }

  pub fn eval_at_one(&self) -> FpVar<Fr> {
    let mut res = self.coeffs[0].clone();
    for i in 1..self.coeffs.len() {
      res = &res + &self.coeffs[i];
    }
    res
  }

  // mul without reduce
  pub fn evaluate(&self, r: &FpVar<Fr>) -> FpVar<Fr> {
    let mut eval = self.coeffs[0].clone();
    let mut power = r.clone();

    for i in 1..self.coeffs.len() {
      eval += &power * &self.coeffs[i];
      power *= r;
    }
    eval
  }
}

#[derive(Clone)]
pub struct SumcheckVerificationCircuit {
  pub polys: Vec<UniPoly>,
}

impl SumcheckVerificationCircuit {
  fn verifiy_sumcheck(
    &self,
    poly_vars: &[UniPolyVar],
    claim_var: &FpVar<Fr>,
    transcript_var: &mut PoseidonTranscripVar,
  ) -> Result<(FpVar<Fr>, Vec<FpVar<Fr>>), SynthesisError> {
    let mut e_var = claim_var.clone();
    let mut r_vars: Vec<FpVar<Fr>> = Vec::new();

    for (poly_var, _poly) in poly_vars.iter().zip(self.polys.iter()) {
      let res = poly_var.eval_at_one() + poly_var.eval_at_zero();
      res.enforce_equal(&e_var)?;
      transcript_var.append_vector(&poly_var.coeffs)?;
      let r_i_var = transcript_var.challenge()?;
      r_vars.push(r_i_var.clone());
      e_var = poly_var.evaluate(&r_i_var.clone());
    }

    Ok((e_var, r_vars))
  }
}

#[derive(Clone)]
pub struct SparsePolyEntryVar {
  idx: usize,
  val_var: FpVar<Fr>,
}

impl AllocVar<SparsePolyEntry, Fr> for SparsePolyEntryVar {
  fn new_variable<T: Borrow<SparsePolyEntry>>(
    cs: impl Into<Namespace<Fr>>,
    f: impl FnOnce() -> Result<T, SynthesisError>,
    _mode: AllocationMode,
  ) -> Result<Self, SynthesisError> {
    f().and_then(|s| {
      let cs = cs.into();
      let spe: &SparsePolyEntry = s.borrow();
      let val_var = FpVar::<Fr>::new_witness(cs, || Ok(spe.val))?;
      Ok(Self {
        idx: spe.idx,
        val_var,
      })
    })
  }
}

#[derive(Clone)]
pub struct SparsePolynomialVar {
  num_vars: usize,
  Z_var: Vec<SparsePolyEntryVar>,
}

impl AllocVar<SparsePolynomial, Fr> for SparsePolynomialVar {
  fn new_variable<T: Borrow<SparsePolynomial>>(
    cs: impl Into<Namespace<Fr>>,
    f: impl FnOnce() -> Result<T, SynthesisError>,
    mode: AllocationMode,
  ) -> Result<Self, SynthesisError> {
    f().and_then(|s| {
      let cs = cs.into();
      let sp: &SparsePolynomial = s.borrow();
      let mut Z_var = Vec::new();
      for spe in sp.Z.iter() {
        let spe_var = SparsePolyEntryVar::new_variable(cs.clone(), || Ok(spe), mode)?;
        Z_var.push(spe_var);
      }
      Ok(Self {
        num_vars: sp.num_vars,
        Z_var,
      })
    })
  }
}

impl SparsePolynomialVar {
  fn compute_chi(a: &[bool], r_vars: &[FpVar<Fr>]) -> FpVar<Fr> {
    let mut chi_i_var = FpVar::<Fr>::one();
    let one = FpVar::<Fr>::one();
    for (i, r_var) in r_vars.iter().enumerate() {
      if a[i] {
        chi_i_var *= r_var;
      } else {
        chi_i_var *= &one - r_var;
      }
    }
    chi_i_var
  }

  pub fn evaluate(&self, r_var: &[FpVar<Fr>]) -> FpVar<Fr> {
    let mut sum = FpVar::<Fr>::zero();
    for spe_var in self.Z_var.iter() {
      // potential problem
      let bits = &spe_var.idx.get_bits(r_var.len());
      sum += SparsePolynomialVar::compute_chi(bits, r_var) * &spe_var.val_var;
    }
    sum
  }
}

#[derive(Clone)]
pub struct R1CSVerificationCircuit {
  pub num_vars: usize,
  pub num_cons: usize,
  pub input: Vec<Fr>,
  pub input_as_sparse_poly: SparsePolynomial,
  pub evals: (Fr, Fr, Fr),
  pub params: PoseidonParameters<Fr>,
  pub prev_challenge: Fr,
  pub claims_phase2: (Scalar, Scalar, Scalar, Scalar),
  pub eval_vars_at_ry: Fr,
  pub sc_phase1: SumcheckVerificationCircuit,
  pub sc_phase2: SumcheckVerificationCircuit,
  // The point on which the polynomial was evaluated by the prover.
  pub claimed_ry: Vec<Scalar>,
}

impl R1CSVerificationCircuit {
  fn new(config: &VerifierConfig) -> Self {
    Self {
      num_vars: config.num_vars,
      num_cons: config.num_cons,
      input: config.input.clone(),
      input_as_sparse_poly: config.input_as_sparse_poly.clone(),
      evals: config.evals,
      params: config.params.clone(),
      prev_challenge: config.prev_challenge,
      claims_phase2: config.claims_phase2,
      eval_vars_at_ry: config.eval_vars_at_ry,
      sc_phase1: SumcheckVerificationCircuit {
        polys: config.polys_sc1.clone(),
      },
      sc_phase2: SumcheckVerificationCircuit {
        polys: config.polys_sc2.clone(),
      },
      claimed_ry: config.ry.clone(),
    }
  }
}

impl ConstraintSynthesizer<Fr> for R1CSVerificationCircuit {
  fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
    let mut transcript_var =
      PoseidonTranscripVar::new(cs.clone(), &self.params, Some(self.prev_challenge));

    let poly_sc1_vars = self
      .sc_phase1
      .polys
      .iter()
      .map(|p| UniPolyVar::new_variable(cs.clone(), || Ok(p), AllocationMode::Witness).unwrap())
      .collect::<Vec<UniPolyVar>>();

    let poly_sc2_vars = self
      .sc_phase2
      .polys
      .iter()
      .map(|p| UniPolyVar::new_variable(cs.clone(), || Ok(p), AllocationMode::Witness).unwrap())
      .collect::<Vec<UniPolyVar>>();

    let input_vars = self
      .input
      .iter()
      .map(|i| FpVar::<Fr>::new_variable(cs.clone(), || Ok(i), AllocationMode::Witness).unwrap())
      .collect::<Vec<FpVar<Fr>>>();

    let claimed_ry_vars = self
      .claimed_ry
      .iter()
      .map(|r| FpVar::<Fr>::new_variable(cs.clone(), || Ok(r), AllocationMode::Input).unwrap())
      .collect::<Vec<FpVar<Fr>>>();

    transcript_var.append_vector(&input_vars)?;

    let num_rounds_x = self.num_cons.log_2();
    let _num_rounds_y = (2 * self.num_vars).log_2();

    let tau_vars = transcript_var.challenge_vector(num_rounds_x)?;

    let claim_phase1_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(Fr::zero()))?;

    let (claim_post_phase1_var, rx_var) =
      self
        .sc_phase1
        .verifiy_sumcheck(&poly_sc1_vars, &claim_phase1_var, &mut transcript_var)?;

    let (Az_claim, Bz_claim, Cz_claim, prod_Az_Bz_claims) = &self.claims_phase2;

    let Az_claim_var = FpVar::<Fr>::new_input(cs.clone(), || Ok(Az_claim))?;
    let Bz_claim_var = FpVar::<Fr>::new_input(cs.clone(), || Ok(Bz_claim))?;
    let Cz_claim_var = FpVar::<Fr>::new_input(cs.clone(), || Ok(Cz_claim))?;
    let prod_Az_Bz_claim_var = FpVar::<Fr>::new_input(cs.clone(), || Ok(prod_Az_Bz_claims))?;
    let one = FpVar::<Fr>::one();
    let prod_vars: Vec<FpVar<Fr>> = (0..rx_var.len())
      .map(|i| (&rx_var[i] * &tau_vars[i]) + (&one - &rx_var[i]) * (&one - &tau_vars[i]))
      .collect();
    let mut taus_bound_rx_var = FpVar::<Fr>::one();

    for p_var in prod_vars.iter() {
      taus_bound_rx_var *= p_var;
    }

    let expected_claim_post_phase1_var =
      (&prod_Az_Bz_claim_var - &Cz_claim_var) * &taus_bound_rx_var;

    claim_post_phase1_var.enforce_equal(&expected_claim_post_phase1_var)?;

    let r_A_var = transcript_var.challenge()?;
    let r_B_var = transcript_var.challenge()?;
    let r_C_var = transcript_var.challenge()?;

    let claim_phase2_var =
      &r_A_var * &Az_claim_var + &r_B_var * &Bz_claim_var + &r_C_var * &Cz_claim_var;

    let (claim_post_phase2_var, ry_var) =
      self
        .sc_phase2
        .verifiy_sumcheck(&poly_sc2_vars, &claim_phase2_var, &mut transcript_var)?;

    //  Because the verifier checks the commitment opening on point ry outside
    //  the circuit, the prover needs to send ry to the verifier (making the
    //  proof size O(log n)). As this point is normally obtained by the verifier
    //  from the second round of sumcheck, the circuit needs to ensure the
    //  claimed point, coming from the prover, is actually the point derived
    //  inside the circuit. These additional checks will be removed
    //  when the commitment verification is done inside the circuit.
    for (i, r) in claimed_ry_vars.iter().enumerate() {
      ry_var[i].enforce_equal(r)?;
    }

    let input_as_sparse_poly_var = SparsePolynomialVar::new_variable(
      cs.clone(),
      || Ok(&self.input_as_sparse_poly),
      AllocationMode::Witness,
    )?;

    let poly_input_eval_var = input_as_sparse_poly_var.evaluate(&ry_var[1..]);

    let eval_vars_at_ry_var = FpVar::<Fr>::new_input(cs.clone(), || Ok(&self.eval_vars_at_ry))?;

    let eval_Z_at_ry_var =
      (FpVar::<Fr>::one() - &ry_var[0]) * &eval_vars_at_ry_var + &ry_var[0] * &poly_input_eval_var;

    let (eval_A_r, eval_B_r, eval_C_r) = self.evals;

    let eval_A_r_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(eval_A_r))?;
    let eval_B_r_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(eval_B_r))?;
    let eval_C_r_var = FpVar::<Fr>::new_witness(cs, || Ok(eval_C_r))?;

    let scalar_var = &r_A_var * &eval_A_r_var + &r_B_var * &eval_B_r_var + &r_C_var * &eval_C_r_var;

    let expected_claim_post_phase2_var = eval_Z_at_ry_var * scalar_var;
    claim_post_phase2_var.enforce_equal(&expected_claim_post_phase2_var)?;

    Ok(())
  }
}

#[derive(Clone)]
pub struct VerifierConfig {
  pub num_vars: usize,
  pub num_cons: usize,
  pub input: Vec<Fr>,
  pub input_as_sparse_poly: SparsePolynomial,
  pub evals: (Fr, Fr, Fr),
  pub params: PoseidonParameters<Fr>,
  pub prev_challenge: Fr,
  pub claims_phase2: (Fr, Fr, Fr, Fr),
  pub eval_vars_at_ry: Fr,
  pub polys_sc1: Vec<UniPoly>,
  pub polys_sc2: Vec<UniPoly>,
  pub ry: Vec<Scalar>,
}
#[derive(Clone)]
pub struct VerifierCircuit {
  pub inner_circuit: R1CSVerificationCircuit,
  pub inner_proof: GrothProof<I>,
  pub inner_vk: PreparedVerifyingKey<I>,
  pub eval_vars_at_ry: Fr,
  pub claims_phase2: (Fr, Fr, Fr, Fr),
  pub ry: Vec<Fr>,
}

impl VerifierCircuit {
  pub fn new<R: Rng + CryptoRng>(
    config: &VerifierConfig,
    mut rng: &mut R,
  ) -> Result<Self, SynthesisError> {
    let inner_circuit = R1CSVerificationCircuit::new(config);
    let (pk, vk) = Groth16::<I>::setup(inner_circuit.clone(), &mut rng).unwrap();
    let proof = Groth16::<I>::prove(&pk, inner_circuit.clone(), &mut rng)?;
    let pvk = Groth16::<I>::process_vk(&vk).unwrap();
    Ok(Self {
      inner_circuit,
      inner_proof: proof,
      inner_vk: pvk,
      eval_vars_at_ry: config.eval_vars_at_ry,
      claims_phase2: config.claims_phase2,
      ry: config.ry.clone(),
    })
  }
}

impl ConstraintSynthesizer<Fq> for VerifierCircuit {
  fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> ark_relations::r1cs::Result<()> {
    let proof_var = ProofVar::<I, IV>::new_witness(cs.clone(), || Ok(self.inner_proof.clone()))?;
    let (v_A, v_B, v_C, v_AB) = self.claims_phase2;
    let mut pubs = vec![];
    pubs.extend(self.ry);
    pubs.extend(vec![v_A, v_B, v_C, v_AB]);
    pubs.extend(vec![self.eval_vars_at_ry]);
    let bits = pubs
      .iter()
      .map(|c| {
        let bits: Vec<bool> = BitIteratorLE::new(c.into_repr().as_ref().to_vec()).collect();
        Vec::new_witness(cs.clone(), || Ok(bits))
      })
      .collect::<Result<Vec<_>, _>>()?;
    let input_var = BooleanInputVar::<Fr, Fq>::new(bits);

    let vk_var = PreparedVerifyingKeyVar::new_witness(cs, || Ok(self.inner_vk.clone()))?;
    Groth16VerifierGadget::verify_with_processed_vk(&vk_var, &input_var, &proof_var)?
      .enforce_equal(&Boolean::constant(true))?;
    Ok(())
  }
}
