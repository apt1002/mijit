/*!
 * Data structures for tracking register pressure.
 */

use std::{cmp, mem};

use super::super::jit::lowerer::{ALLOCATABLE_REGISTERS};

/**
 * Information recorded about one logical register.
 */
#[derive(Debug, Copy, Clone)]
struct RegInfo<T> {
    /** Earliest time at which this register is written. */
    pub born_cycle: usize,
    /** Time at which the value written in `born_cycle` is last read. */
    pub dies_cycle: usize,
    /** Earliest use site of this register. */
    pub earliest_use: Option<T>,
}

/**
 * Represents register pressure as a function of time, and decides which values
 * to colocate in registers, and which to spill.
 *
 * Registers are identified by small integers.
 * Times are measured in cycles backwards from the end of the schedule.
 *
 * A payload of type `T` can be associated with each register.
 */
pub struct Pressure<T> {
    /** Sorted by `born_cycle`. */
    regs: Vec<RegInfo<T>>,
}

impl<T> Pressure<T> {
    pub fn new() -> Self {
        Pressure {
            regs: (0..ALLOCATABLE_REGISTERS.len()).map (|_| {
                RegInfo {born_cycle: 0, dies_cycle: 0, earliest_use: None}
            }).collect(),
        }
    }

    pub fn latest_time_with_unused_register(&self) -> usize {
        self.regs.iter().fold(usize::MAX, |cycle, ri| {
            cmp::min(ri.born_cycle, cycle)
        })
    }

    /**
     * Select a register to hold a value from `born_cycle` to `dies_cycle`, and
     * mark it as unavailable during that interval, used for `use_`.
     *
     * Returns one of the following:
     *
     *  - Some((r, None)): use register `r`, which is not yet used.
     *  - Some((r, Some(previous_use))): use register `r`; this replaces its
     *  `previous_use`, which will have to use a spill slot instead.
     *  - None: no register is available; use a spill slot instead.
     */
    pub fn allocate_register(
        &mut self,
        born_cycle: usize,
        dies_cycle: usize,
        use_: T,
    ) -> Option<(usize, Option<T>)> {
        // Choose an available register.
        if let (Some(r), _) = self.regs.iter().enumerate().filter_map(|(i, ri)| {
            // Get indices of registers that are unused for the entire range.
            if ri.born_cycle <= dies_cycle { Some(i) } else { None }
        }).fold((None, 0), |(i, i_cycle), j| {
            // Find the one born earliest.
            let j_cycle = self.regs[j].born_cycle;
            if i_cycle >= j_cycle { (i, i_cycle) } else { (Some(j), j_cycle) }
        }) {
            // We found one.
            return Some((r, None));
        }
        // There wasn't one: find a register to spill.
        if let (Some(r), _) = self.regs.iter().enumerate().filter_map(|(i, ri)| {
            // Get indices of registers that die after us.
            if ri.dies_cycle < dies_cycle { Some(i) } else { None }
        }).fold((None, usize::MAX), |(i, i_cycle), j| {
            // Find the one that dies latest.
            let j_cycle = self.regs[j].dies_cycle;
            if i_cycle < j_cycle { (i, i_cycle) } else { (Some(j), j_cycle) }
        }) {
            // We found one.
            let mut info = RegInfo {
                born_cycle,
                dies_cycle,
                earliest_use: Some(use_),
            };
            mem::swap(&mut info, &mut self.regs[r]);
            return Some((r, info.earliest_use));
        }
        // There wasn't one: spill ourself.
        None
    }    
}
