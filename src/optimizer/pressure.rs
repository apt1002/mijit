/*!
 * Data structures for tracking register pressure.
 */

use std::{cmp, mem, ops};
use ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign};

use super::super::jit::lowerer::{ALLOCATABLE_REGISTERS};

/**
 * Represents the lifetime of a value. `T` is the type of time.
 *
 * The operators `|` and `&` compute the union and intersection of Lifes. Note
 * that the union of `Life {born: 1, dies: 2}` and `Life {born: 3, dies: 4}` is
 * `Life {born: 1, dies: 4}`; the gap from `2` to `3` is glossed over.
 *
 * The empty Life can be represented by putting a maximal time in `born`
 * and a minimal time in `dies`.
 */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Life<T: Ord> {
    pub born: T,
    pub dies: T,
}

impl<T: Ord> Life<T> {
    pub fn new(born: T, dies: T) -> Self {
        Life {born, dies}
    }

    /** Tests whether there is time that `self` and `other` both contain. */
    pub fn overlaps(&self, other: &Self) -> bool {
        self.born < other.dies && other.born < self.dies
    }

    /** Tests whether all times in `other` are also in `self`. */
    pub fn contains(&self, other: &Self) -> bool {
        self.born <= other.born && other.dies <= self.dies
    }

    /** Tests `born > dies`. */
    pub fn is_empty(&self) -> bool {
        self.born > self.dies
    }
}

impl<T: Ord> BitAndAssign for Life<T> {
    fn bitand_assign(&mut self, rhs: Self) {
        if rhs.born > self.born { self.born = rhs.born }
        if rhs.dies < self.dies { self.dies = rhs.dies }
    }
}

impl<T: Ord> BitAnd for Life<T> {
    type Output = Self;

    fn bitand(mut self, rhs: Self) -> Self {
        self.bitor_assign(rhs);
        self
    }
}

impl<T: Ord> BitOrAssign for Life<T> {
    fn bitor_assign(&mut self, rhs: Self) {
        if rhs.born < self.born { self.born = rhs.born }
        if rhs.dies > self.dies { self.dies = rhs.dies }
    }
}

impl<T: Ord> BitOr for Life<T> {
    type Output = Self;

    fn bitor(mut self, rhs: Self) -> Self {
        self.bitor_assign(rhs);
        self
    }
}

//-----------------------------------------------------------------------------

/**
 * Return the index in `it` of the element for which `f` gives the largest
 * non-None result.
 */
fn map_filter_max<I: IntoIterator, T: Ord> (
    it: I,
    mut f: impl FnMut(I::Item) -> Option<T>,
) -> Option<usize> {
    let it = it.into_iter().enumerate();
    // Apply `f` to every element and filter out the `None` results.
    let mut it = it.filter_map(|(i, x)| f(x).map(|fx| (i, fx)));
    // Take the first element, if any.
    it.next().map(|ifx| {
        // There is at least one non-None result: `ifx`. Compare to the rest.
        it.fold(ifx, |ifx, jfy| {
            if ifx.1 > jfy.1 { ifx } else { jfy }
        }).0
    })
}

/**
 * Information recorded about one logical register.
 */
#[derive(Debug, Copy, Clone)]
struct RegInfo<T: Ord, U> {
    /** The lifetime of the earliest use of this register. */
    pub life: Life<T>,
    /** Earliest use site of this register, if any. */
    pub use_: Option<U>,
}

/**
 * Represents register pressure as a function of time, and decides which values
 * to colocate in registers, and which to spill.
 *
 * For simplicity, we make the approximation that if a register is used at time
 * `t` then it is also used at all later times. Therefore, we only need to
 * represent pressure as an increasing function of time.
 *
 * Registers are identified by small integers. We call these "logical"
 * registers, to emphasize that there is no particular mapping to physical
 * registers.
 *
 * `T` is the type of time.
 * A payload of type `U` can be associated with each register. The payload
 * represents the earliest use site of the register.
 */
pub struct Pressure<T: Ord, U> {
    /** Indexed by register number. */
    regs: Vec<RegInfo<T, U>>,
}

impl<T: Ord, U> Pressure<T, U> {
    /** Initially, all registers are free until `end_time()`. */
    pub fn new(end_time: impl Fn() -> T) -> Self {
        Pressure {
            regs: (0..ALLOCATABLE_REGISTERS.len()).map (|_| RegInfo {
                life: Life::new(end_time(), end_time()),
                use_: None,
            }).collect(),
        }
    }

    pub fn latest_time_with_unused_register(&self) -> &T {
        let mut it = self.regs.iter().map(|ri| &ri.life.born);
        let x = it.next().expect("No registers");
        it.fold(x, cmp::max)
    }

    /**
     * Select a register to hold a value during `life`, and mark it as
     * unavailable during that interval, used at site `use_`.
     *
     * Returns one of the following:
     *
     *  - Some((r, None)): use register `r`, which is not yet used.
     *  - Some((r, Some(previous_use))): use register `r`; this replaces its
     *  `previous_use`, which will have to use a spill slot instead.
     *  - None: no register is available; use a spill slot instead.
     */
    pub fn allocate_register(&mut self, life: Life<T>, use_: U) -> Option<(usize, Option<U>)> {
        // Choose an available register.
        // Consider registers that are born later than `life`.
        // Find the one born earliest.
        if let Some(r) = map_filter_max(&self.regs, |ri| {
            if ri.life.born >= life.dies { Some(cmp::Reverse(&ri.life.born)) } else { None }
        }) {
            // We found one.
            self.regs[r] = RegInfo {life, use_: Some(use_)};
            return Some((r, None));
        }
        // There wasn't one. Find a register to spill.
        // Consider registers that die after us.
        // Find the one that dies latest.
        if let Some(r) = map_filter_max(&self.regs, |ri| {
            if ri.life.dies > life.dies { Some(&ri.life.dies) } else { None }
        }) {
            // We found one.
            let mut info = RegInfo {life, use_: Some(use_)};
            mem::swap(&mut info, &mut self.regs[r]);
            return Some((r, info.use_));
        }
        // There wasn't one: spill ourself.
        None
    }    
}
