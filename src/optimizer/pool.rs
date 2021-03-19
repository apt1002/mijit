use crate::util::{ArrayMap, map_filter_max};
use super::{NUM_REGISTERS, RegIndex};

/**
 * A pool of allocatable Registers.
 *
 * Every register is classified as "clean" or "dirty". A register is dirty
 * if it holds the only copy of some value. If it is unused or if it has been
 * spilled then it is clean.
 *
 * Each register is annotated with a `D` if it is dirty.
 */
#[derive(Debug)]
pub struct RegisterPool<D> {
    /** For each register, its annotation if dirty, otherwise `None`. */
    dirty: ArrayMap<RegIndex, Option<D>>,
    /** All clean registers in the order they became clean. */
    clean: Vec<RegIndex>,
}

impl<D> RegisterPool<D> {
    /**
     * Initialise a `RegisterPool` with specified dirty [`Value`]s.
     * Non-Registers are ignored.
     * Each clean register `ri` is annotated with `c(ri)`.
     */
    pub fn new(dirty: ArrayMap<RegIndex, Option<D>>) -> Self {
        // Enumerate the clean registers.
        let mut clean = Vec::with_capacity(NUM_REGISTERS);
        for i in 0..NUM_REGISTERS {
            let ri = RegIndex(i);
            if dirty[ri].is_none() {
                clean.push(ri);
            }
        }
        // Return.
        RegisterPool {dirty, clean}
    }

    /** Tests whether the specified register is clean. */
    pub fn is_clean(&self, ri: RegIndex) -> bool {
        self.dirty[ri].is_none()
    }

    /**
     * Returns the number of clean registers. The rest are dirty.
     * Decreased by `allocate()`. Increased by `spill()`.
     */
    pub fn num_clean(&self) -> usize { self.clean.len() }

    /**
     * Allocates and returns a register, marks it as dirty, and annotates it
     * with `d`. Registers are allocated in LIFO order.
     * Panics if there is no clean register available.
     */
    pub fn allocate(&mut self, d: D) -> RegIndex {
        let ri = self.clean.pop().expect("No register is clean");
        let d = self.dirty[ri].replace(d);
        assert!(d.is_none());
        ri
    }

    /**
     * Marks the specified register as clean, and annotates it with `c`.
     * Panics if `ri` is not dirty.
     */
    pub fn free(&mut self, ri: RegIndex) -> D {
        let d = self.dirty[ri].take().expect("Register is not dirty");
        self.clean.push(ri);
        d
    }

    /**
     * Finds, frees and returns the dirty register for which `priority()`
     * returns the largest value.
     * Panics if there is no dirty register available.
     */
    pub fn spill<P: Ord>(&mut self, priority: impl Fn(&D) -> P) -> (RegIndex, D) {
        // This is `Option::map()` but it avoids `priority: impl Copy`.
        let p = |d: &Option<D>| match d {
            &None => None,
            &Some(ref d) => Some(priority(d)),
        };
        let i = map_filter_max(&self.dirty, p);
        let ri = RegIndex(i.expect("No register is dirty"));
        let d = self.free(ri);
        (ri, d)
    }
}
