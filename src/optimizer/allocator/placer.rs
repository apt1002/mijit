use std::fmt::{Debug};
use std::ops::{Add, AddAssign};

use super::{Resources, BUDGET};
use crate::util::{AsUsize};

array_index! {
    /// A time in cycles. We are agnostic as to whether `Time` runs forwards or
    /// backwards; you can use it to generate code in either direction.
    /// Therefore, we use the terminology "larger" and "smaller", not "earlier"
    /// or "later".
    #[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Time(std::num::NonZeroUsize) {
        debug_name: "Time",
        UInt: usize,
    }
}

impl Time {
    pub fn max_with(&mut self, other: Time) {
        *self = std::cmp::max(*self, other);
    }
}

/// The least time (zero).
pub const LEAST: Time = unsafe {Time::new_unchecked(0)};

impl Default for Time {
    fn default() -> Self { LEAST }
}

impl Add<usize> for Time {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        Time::new(self.as_usize() + rhs).expect("Overflow")
    }
}

impl AddAssign<usize> for Time {
    fn add_assign(&mut self, other: usize) {
        *self = self.add(other);
    }
}

//-----------------------------------------------------------------------------

/// The maximum number of items to place per cycle.
const MAX_ITEMS: usize = 8;

/// Represents a list of items that have been placed in the same clock cycle.
#[derive(Debug)]
struct Cycle<T> {
    /// The CPU resources unused in this `Cycle`.
    remaining: Resources,
    /// The number of items in `items`.
    num_items: usize,
    /// The items to place in this `Cycle`.
    items: [Option<T>; MAX_ITEMS],
}

impl<T> Cycle<T> {
    /// Constructs an empty `Cycle` with [`BUDGET`] remaining.
    pub fn new() -> Self {
        Cycle {
            remaining: BUDGET,
            num_items: 0,
            items: Default::default(),
        }
    }

    /// Append `item` to this `Cycle`.
    /// Panics if `num_items` exceeds `MAX_ITEMS`.
    pub fn push(&mut self, item: T) {
        self.items[self.num_items] = Some(item);
        self.num_items += 1;
    }

    /// Yields the items in this `Cycle` in the order they were pushed.
    pub fn iter(&self) -> impl Iterator<Item = &'_ T> {
        self.items[0..self.num_items].iter().map(Option::as_ref).map(Option::unwrap)
    }
}

//-----------------------------------------------------------------------------

/// Represents an allocation of items to clock cycles.
#[derive(Debug)]
pub struct Placer<T: Debug> {
    /// The Cycles in which we're placing things.
    cycles: Vec<Cycle<T>>,
}

impl<T: Debug> Default for Placer<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Debug> Placer<T> {
    pub fn new() -> Self {
        Placer {
            cycles: Vec::new(),
        }
    }

    fn len(&self) -> Time {
        Time::new(self.cycles.len()).expect("Overflow")
    }

    fn at(&mut self, time: Time) -> &mut Cycle<T> {
        while self.len() <= time {
            self.cycles.push(Cycle::new());
        }
        &mut self.cycles[time.as_usize()]
    }

    /// Decide when to place `item`. On entry, `*time` is the least time
    /// that is acceptable. `*time` is increased as necessary to find a clock
    /// cycle that can afford `cost`.
    pub fn add_item(&mut self, item: T, cost: Resources, time: &mut Time) {
        #[allow(clippy::neg_cmp_op_on_partial_ord)]
        while !(cost <= self.at(*time).remaining) {
            *time += 1;
        }
        self.at(*time).remaining -= cost;
        self.at(*time).push(item);
    }

    /// Yields all the items in the chosen order.
    pub fn iter(&self) -> impl Iterator<Item=&T> {
        self.cycles.iter().flat_map(|c| c.iter())
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::{SPILL_COST};

    #[test]
    fn grow() {
        let mut p = Placer::new();
        // Overflow `BUDGET` to force the Placer to grow.
        for _ in 0..100 {
            let mut time = LEAST;
            p.add_item('A', SPILL_COST, &mut time);
        }
    }
}
