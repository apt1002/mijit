//! Ranges of values using clock arithmetic.

use std::cmp::{Ord};
use std::convert::{TryFrom};

/// Describes a reason why a Range cannot be constructed.
pub enum Error {
    /// The Range would contain no values.
    Empty,
    /// The Range would contain all values.
    Full,
    /// The Range would consists of more than one interval.
    Discontiguous,
}

use Error::*;

/**
 * A range of values from `start` (inclusive) to `end` (exclusive), in clock
 * arithmetic. Exchanging `start` and `end` inverts the range. See `contains()`
 * for a formal definition.
 *
 * `Range(start, end).contains(x)` is unchanged on adding a constant to all of
 * `x`, `start` and `end`, even using clock arithmetic (a.k.a. modular
 * arithmetic, wrapping arithmetic). Therefore, this type can represent signed
 * and unsigned integer ranges in a unified way.
 *
 * The case `start == end` is forbidden. Represent the full and empty ranges
 * in some other way.
 */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Range<T: Ord>(T, T);

impl<T: Ord> Range<T> {
    /**
     * Constructs a Range that includes the values from `start` upwards, and
     * excludes the values from `end` upwards.
     */
    pub fn new(start: T, end: T) -> Result<Self, Error> {
        if start == end { return Err(Empty); }
        Ok(Range(start, end))
    }

    /**
     * `x` is in the range iff `x < start` xor `x < end` xor `end < start`.
     */
    pub fn contains(&self, x: T) -> bool {
        (x < self.0) ^ (x < self.1) ^ (self.1 < self.0)
    }
}

impl<T: Clone + Ord> Range<T> {
    pub fn start(&self) -> T { self.0.clone() }
    pub fn end(&self) -> T { self.1.clone() }

    pub fn not(&self) -> Self {
        Range(self.1.clone(), self.0.clone())
    }

//    pub fn and(&self, &other: Self) -> Result<Self, Error> {
//    }
}

impl<T: Ord> TryFrom<std::ops::Range<T>> for Range<T> {
    type Error = Error;

    fn try_from(t: std::ops::Range<T>) -> Result<Self, Error> {
        if t.end <= t.start { return Err(Empty); }
        Range::new(t.start, t.end)
    }
}

// Integer-only.

/** Functionality available for types with a minimum value. */
macro_rules! impl_min {
    ($t: ty) => {
        impl TryFrom<std::ops::RangeFrom<$t>> for Range<$t> {
            type Error = Error;

            fn try_from(range: std::ops::RangeFrom<$t>) -> Result<Self, Error> {
                Range::new(range.start, <$t>::MIN)
            }
        }

        impl TryFrom<std::ops::RangeTo<$t>> for Range<$t> {
            type Error = Error;

            fn try_from(range: std::ops::RangeTo<$t>) -> Result<Self, Error> {
                Range::new(<$t>::MIN, range.end)
            }
        }
    }
}

/** Functionality available for integer types. */
macro_rules! impl_int {
    ($u: ty, $i: ty) => {
        impl_min!($u);
        impl_min!($i);

        impl Range<$u> {
            /** Returns a range that contains `x as $signed` iff `self` contains `x`. */
            pub fn signed(self) -> Range<$i> {
                Range(self.0 as $i, self.1 as $i)
            }
        }

        impl Range<$i> {
            /** Returns a range that contains `x as $unsigned` iff `self` contains `x`. */
            pub fn unsigned(self) -> Range<$u> {
                Range(self.0 as $u, self.1 as $u)
            }
        }
    }
}

impl_int!(u8, i8);
impl_int!(u16, i16);
impl_int!(u32, i32);
impl_int!(u64, i64);
