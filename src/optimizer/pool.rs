use crate::util::{ArrayMap};
use super::{NUM_REGISTERS, RegIndex};

/**
 * A pool of allocatable Registers.
 *
 * Every register is classified as "clean" or "dirty". A register is dirty
 * if it holds the only copy of some value. If it is unused or if it has been
 * spilled then it is clean.
 */
#[derive(Debug)]
pub struct RegisterPool {
    /** For each register, `true` if dirty. */
    dirty: ArrayMap<RegIndex, bool>,
    /** All clean registers in the order they became clean. */
    clean: Vec<RegIndex>,
}

impl RegisterPool {
    /**
     * Initialise a `RegisterPool` with specified dirty [`Value`]s.
     * Non-Registers are ignored.
     * Each clean register `ri` is annotated with `c(ri)`.
     */
    pub fn new(dirty: ArrayMap<RegIndex, bool>) -> Self {
        // Enumerate the clean registers.
        let mut clean = Vec::with_capacity(NUM_REGISTERS);
        for i in 0..NUM_REGISTERS {
            let ri = RegIndex(i);
            if !dirty[ri] {
                clean.push(ri);
            }
        }
        // Return.
        RegisterPool {dirty, clean}
    }

    /** Tests whether the specified register is clean. */
    pub fn is_clean(&self, ri: RegIndex) -> bool {
        !self.dirty[ri]
    }

    /**
     * Returns the number of clean registers. The rest are dirty.
     * Decreased by `allocate()`. Increased by `spill()`.
     */
    pub fn num_clean(&self) -> usize { self.clean.len() }

    /**
     * Allocates and returns a register, which it marks as dirty.
     * Registers are allocated in LIFO order.
     * Panics if there is no clean register available.
     */
    pub fn allocate(&mut self) -> RegIndex {
        let ri = self.clean.pop().expect("No register is clean");
        assert!(!self.dirty[ri]);
        self.dirty[ri] = true;
        ri
    }

    /**
     * Marks the specified register as clean. Panics if `ri` is not dirty.
     */
    pub fn free(&mut self, ri: RegIndex) {
        assert!(self.dirty[ri]);
        self.dirty[ri] = false;
        self.clean.push(ri);
    }
}
