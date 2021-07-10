use super::code::{Precision};
use crate::util::{rotate_left};

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

// ----------------------------------------------------------------------------

/** A reason why a constant is not encodable as a [`LogicImmediate`]. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum LogicImmediateError {AllSame, NonRepeating}

/**
 * Represents a legal "logic immediate". The [encoding] is quite esoteric.
 *
 * [encoding]: https://dinfuehr.github.io/blog/encoding-of-immediate-values-on-aarch64/
 */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct LogicImmediate {prec: Precision, encoding: u32}

impl LogicImmediate {
    #[allow(clippy::many_single_char_names)]
    pub fn new(prec: Precision, mut x: u64) -> Result<Self, LogicImmediateError> {
        // Here we use the ARM's terminology; see `DecodeBitMasks()` in the
        // [ARMv8 Architecture Reference Manual] (on page 7954).
        //
        // [ARMv8 Architecture Reference Manual]: https://documentation-service.arm.com/static/60119835773bb020e3de6fee
        if prec == Precision::P32 {
            // Only the bottom 32 bits of `x` are significant.
            // Encode as if the top 32 bits are the same.
            x &= 0xFFFFFFFF;
            x |= x << 32;
        }
        // `0` and `-1` are not encodable.
        if x == 0 || x == !0 { return Err(LogicImmediateError::AllSame); }
        // Count the first four runs of binary digits.
        let num_zeros = x.leading_zeros();
        x = rotate_left(x, num_zeros);
        let num_ones = (!x).leading_zeros();
        x = rotate_left(x, num_ones);
        let mut y = x;
        let num_zeros2 = y.leading_zeros();
        y = rotate_left(y, num_zeros2);
        let num_ones2 = (!y).leading_zeros();
        y = rotate_left(y, num_ones2);
        // `num_zeros2 + num_ones2` should be a whole repeating unit.
        if x != y { return Err(LogicImmediateError::NonRepeating); }
        // The repeat length should be a power of two and not `1`.
        let esize = num_zeros2 + num_ones2;
        if !esize.is_power_of_two() || esize < 2 {
            // Unreachable?
            return Err(LogicImmediateError::NonRepeating);
        }
        // `num_zeros + num_ones` undid `ROR(welem, r)`.
        let r = num_zeros + num_ones;
        assert!(r <= esize);
        // `num_ones2` undid `Ones(s + 1)`.
        let s = num_ones2 - 1;
        assert!(s < esize);
        // Encode.
        let imms = (128 - 2 * esize + s) & 0x3F;
        let immr = r & (esize - 1);
        let n = (esize == 64) as u32;
        Ok(Self {prec, encoding: (n << 12) | (immr << 6) | imms})
    }

    pub fn prec(self) -> Precision { self.prec }

    pub fn encoding(self) -> u32 { self.encoding }
}

// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn logic_immediate() {
        use Precision::*;

        fn check(prec: Precision, val: u64, expected: u32) {
            assert_eq!(
                LogicImmediate::new(prec, val).unwrap().encoding(),
                expected,
            );
        }

        // Exhaustively enumerate all encodable immediates.
        for prec in [P32, P64] {
            for (size, imms_size_bits, imms_length_mask) in [
                ( 2, 0b111100, 0b000001),
                ( 4, 0b111000, 0b000011),
                ( 8, 0b110000, 0b000111),
                (16, 0b100000, 0b001111),
                (32, 0b000000, 0b011111),
                (64, 0b000000, 0b111111),
            ] {
                if size == 64 && prec == P32 {
                    // There are no 32-bit constants with a size of 64.
                    continue;
                }
                for length in 0..imms_length_mask {
                    let pattern = (0..64).step_by(size as usize).fold(
                        (1 << (length + 1)) - 1,
                        |acc, shift| acc | (acc << shift));
                    for rotation in 0..size {
                        let mut val = crate::util::rotate_right(pattern, rotation);
                        if prec == P32 { val >>= 32 };
                        let n = (size == 64) as u32;
                        let immr = rotation;
                        let imms = imms_size_bits | length;
                        let encoding = (n << 12) | (immr << 6) | imms;
                        check(prec, val, encoding);
                    }
                }
            }
        }
        // Check some notable non-encodable immediates.
        use LogicImmediateError::*;
        assert_eq!(LogicImmediate::new(P32, 0x00000000), Err(AllSame));
        assert_eq!(LogicImmediate::new(P32, 0xFFFFFFFF), Err(AllSame));
        assert_eq!(LogicImmediate::new(P32, 0x5A5A5A5A), Err(NonRepeating));
        assert_eq!(LogicImmediate::new(P32, 0x00000005), Err(NonRepeating));
        assert_eq!(LogicImmediate::new(P64, 0x0000000000000000), Err(AllSame));
        assert_eq!(LogicImmediate::new(P64, 0xFFFFFFFFFFFFFFFF), Err(AllSame));
        assert_eq!(LogicImmediate::new(P64, 0x5A5A5A5A5A5A5A5A), Err(NonRepeating));
        assert_eq!(LogicImmediate::new(P64, 0x0000000000000005), Err(NonRepeating));
    }
}
