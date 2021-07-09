use std::fmt::{Debug};
use std::ops::{Add, AddAssign};

use super::{Resources, BUDGET};
use crate::util::{AsUsize};

array_index! {
    /**
     * A time in cycles. We are agnostic as to whether `Time` runs forwards or
     * backwards; you can use it to generate code in either direction.
     * Therefore, we use the terminology "larger" and "smaller", not "earlier"
     * or "later".
     */
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

/** The least time (zero). */
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

/** The maximum number of items to place per cycle. */
pub const MAX_ITEMS: usize = 8;

/**
 * Represents a list of items that have been placed in the same cycle.
 */
#[derive(Debug)]
struct Cycle<T: Default> {
    /** The CPU resources unused in this `Cycle`. */
    remaining: Resources,
    /** The number of items in `items`. */
    num_items: usize,
    /** The items to place in this `Cycle`. */
    items: [T; MAX_ITEMS],
}

impl<T: Default> Cycle<T> {
    /** Constructs an empty `Cycle` with [`BUDGET`] remaining. */
    pub fn new() -> Self {
        Cycle {
            remaining: BUDGET,
            num_items: 0,
            items: Default::default(),
        }
    }
}

//-----------------------------------------------------------------------------

/** Represents an allocation of instructions to clock cycles. */
#[derive(Debug)]
pub struct Placer<T: Debug + Default> {
    /** The Cycles in which we're placing things. */
    cycles: Vec<Cycle<T>>,
}

impl<T: Debug + Default> Default for Placer<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Debug + Default> Placer<T> {
    pub fn new() -> Self {
        Placer {
            cycles: Vec::new(),
        }
    }

    fn len(&self) -> Time {
        Time::new(self.cycles.len()).expect("Overflow")
    }

    fn at(&mut self, cycle: Time) -> &mut Cycle<T> {
        &mut self.cycles[cycle.as_usize()]
    }

    /** Find a cycle that can afford `cost`, and subtract `cost` from it. */
    fn choose_cycle(&mut self, cost: Resources, cycle: &mut Time) {
        #[allow(clippy::neg_cmp_op_on_partial_ord)]
        while *cycle < self.len() && !(cost <= self.at(*cycle).remaining) {
            *cycle += 1;
        }
        while self.len() <= *cycle {
            self.cycles.push(Cycle::new());
        }
        self.at(*cycle).remaining -= cost;
    }

    /**
     * Decide when to place `item`. On entry, `*cycle` is the least time
     * that is acceptable. `*cycle` is increased as necessary to find a cycle
     * that can afford `cost`.
     */
    pub fn add_item(&mut self, item: T, cost: Resources, cycle: &mut Time) {
        self.choose_cycle(cost, cycle);
        let c = &mut self.at(*cycle);
        assert!(c.num_items < MAX_ITEMS);
        c.items[c.num_items] = item;
        c.num_items += 1;
    }

    pub fn iter(&self) -> impl Iterator<Item=&T> {
        self.cycles.iter().flat_map(|c: &Cycle<T>| {
            c.items[0..c.num_items].iter()
        })
    }
}
