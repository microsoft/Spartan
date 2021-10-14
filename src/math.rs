pub trait Math {
  fn square_root(self) -> usize;
  fn pow2(self) -> usize;
  fn get_bits(self, num_bits: usize) -> Vec<bool>;
}

impl Math for usize {
  #[inline]
  fn square_root(self) -> usize {
    (self as f64).sqrt() as usize
  }

  #[inline]
  fn pow2(self) -> usize {
    let base: usize = 2;
    base.pow(self as u32)
  }

  /// Returns the num_bits from n in a canonical order
  fn get_bits(self, num_bits: usize) -> Vec<bool> {
    (0..num_bits)
      .map(|shift_amount| ((self & (1 << (num_bits - shift_amount - 1))) > 0))
      .collect::<Vec<bool>>()
  }
}
