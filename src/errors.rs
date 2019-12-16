use std::fmt;

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
