use crate::util::{ArrayMap};
use super::{NUM_REGISTERS, all_registers};
use super::code::{Register};

/**
 * A pool of allocatable [`Register`]s.
 *
 * Every `Register` is classified as "clean" or "dirty". A `Register` is dirty
 * if it holds the only copy of some value. If it is unused or if it has been
 * spilled then it is clean.
 */
#[derive(Debug)]
#[allow(clippy::module_name_repetitions)]
pub struct RegisterPool {
    /** For each [`Register`], `true` if dirty. */
    dirty: ArrayMap<Register, bool>,
    /** All clean registers in the order they became clean. */
    clean: Vec<Register>,
}

impl RegisterPool {
    /**
     * Initialise a `RegisterPool` with specified dirty [`Value`]s.
     * Non-Registers are ignored.
     */
    pub fn new(dirty: ArrayMap<Register, bool>) -> Self {
        // Enumerate the clean registers.
        let mut clean = Vec::with_capacity(NUM_REGISTERS);
        for reg in all_registers() {
            if !dirty[reg] {
                clean.push(reg);
            }
        }
        // Return.
        RegisterPool {dirty, clean}
    }

    /** Tests whether the specified [`Register`] is clean. */
    pub fn is_clean(&self, reg: Register) -> bool {
        !self.dirty[reg]
    }

    /**
     * Returns the number of clean [`Register`]s. The rest are dirty.
     * Decreased by `allocate()`. Increased by `spill()`.
     */
    pub fn num_clean(&self) -> usize { self.clean.len() }

    /**
     * Allocates and returns a [`Register`], which it marks as dirty.
     * `Register`s are allocated in LIFO order.
     * Panics if there is no clean `Register` available.
     */
    pub fn allocate(&mut self) -> Register {
        let reg = self.clean.pop().expect("No register is clean");
        assert!(!self.dirty[reg]);
        self.dirty[reg] = true;
        reg
    }

    /**
     * Marks the specified [`Register`] as clean. Panics if `reg` is not dirty.
     */
    pub fn free(&mut self, reg: Register) {
        assert!(self.dirty[reg]);
        self.dirty[reg] = false;
        self.clean.push(reg);
    }
}
