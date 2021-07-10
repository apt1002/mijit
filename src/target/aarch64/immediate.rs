use super::code::{Precision};

/**
 * Represents a [`Precision`] and an amount to shift by.
 * The shift amount is between `0` and `31` inclusive for `P32`, and between
 * `0` and `63` inclusive for `P64`.
 */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Shift {prec: Precision, amount: u32}

impl Shift {
    pub const fn new(prec: Precision, amount: u64) -> Result<Self, ()> {
        let num_bits = 5 + (prec as usize);
        let limit = 1 << num_bits;
        if amount >= limit { return Err(()); }
        Ok(Self {prec: prec, amount: amount as u32})
    }

    pub const fn prec(self) -> Precision { self.prec }

    pub const fn amount(self) -> u32 { self.amount }
}

// ----------------------------------------------------------------------------

/** Represents an unsigned `N`-bit integer. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Unsigned<const N: usize>(u32);

impl<const N: usize> Unsigned<N> {
    pub fn new(value: u64) -> Result<Self, ()> {
        let _ = 32 - N; // Static assertion: N <= 32.
        let limit = 1 << N;
        if value >= limit { return Err(()); }
        Ok(Self(value as u32))
    }

    pub fn as_u32(self) -> u32 { self.0 }
}
