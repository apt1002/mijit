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

