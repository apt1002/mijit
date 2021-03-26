use std::fmt::{Debug};

use super::{Resources, BUDGET};

/** The maximum number of [`Item`]s to place per cycle. */
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
    /** Constructs an empty Cycle with `BUDGET` remaining. */
    pub fn new() -> Self {
        Cycle {
            remaining: BUDGET,
            num_items: 0,
            items: Default::default(),
        }
    }
}

/**
 * Represents an allocation of instructions to clock cycles.
 *
 * This data structure is agnostic as to whether time runs forwards or
 * backwards; you can use it to generate code in either direction. Therefore,
 * we use the terminology "larger" and "smaller", not "earlier" or "later".
 */
#[derive(Debug)]
pub struct Placer<T: Debug + Default> {
    /** The Cycles in which we're placing things. */
    cycles: Vec<Cycle<T>>,
}

impl<T: Debug + Default> Placer<T> {
    pub fn new() -> Self {
        Placer {
            cycles: Vec::new(),
        }
    }

    /** Find a cycle that can afford `cost`, and subtract `cost` from it. */
    fn choose_cycle(&mut self, cost: Resources, cycle: &mut usize) {
        while *cycle < self.cycles.len() && !(cost <= self.cycles[*cycle].remaining) {
            *cycle += 1;
        }
        while self.cycles.len() <= *cycle {
            self.cycles.push(Cycle::new());
        }
        self.cycles[*cycle].remaining -= cost;
    }

    /**
     * Decide when to place `item`. On entry, `*cycle` is the least time
     * that is acceptable. `*cycle` is increased as necessary to find a cycle
     * that can afford `cost`.
     */
    pub fn add_item(&mut self, item: T, cost: Resources, cycle: &mut usize) {
        assert_ne!(*cycle, usize::MAX);
        self.choose_cycle(cost, cycle);
        let c = &mut self.cycles[*cycle];
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
