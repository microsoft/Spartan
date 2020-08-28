use core::fmt;

pub struct ProofVerifyError;

impl fmt::Display for ProofVerifyError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "Proof verification failed")
  }
}

impl fmt::Debug for ProofVerifyError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{{ file: {}, line: {} }}", file!(), line!())
  }
}

pub enum R1CSError {
  NonPowerOfTwoCons,
  NonPowerOfTwoVars,
  InvalidNumberOfInputs,
  InvalidScalar,
}

impl fmt::Display for R1CSError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "R1CSError")
  }
}

impl fmt::Debug for R1CSError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{{ file: {}, line: {} }}", file!(), line!())
  }
}
