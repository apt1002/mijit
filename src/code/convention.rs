use super::{Global, Variable, Action};

/**
 * Represents the convention by which code passes values to a label. The
 * concept is similar to a calling convention, but it's for a jump, not a call.
 *
 * This is a place-holder. Possible future uses:
 *  - Knowledge about values, e.g. minimum and maximum possible value, and
 *    which bits are known to be set or clear.
 *  - Knowledge about possible common sub-expressions, e.g. knowing that some
 *    value is the difference of two other values.
 *  - Knowledge about the cache state, e.g. that some value is the value of
 *    some memory location, and whether it needs to be stored.
 */
#[derive(Debug, Clone)]
pub struct Convention {
    /** The values that are live on entry. */
    pub live_values: Box<[Variable]>,
    /** The number of spill [`Slot`]s used by the `Convention`. */
    pub slots_used: usize,
}

/**
 * Returns a [`Convention`] with no [`Slot`]s, no live [`Register`]s, and the
 * specified number of [`Global`]s.
 */
pub fn empty_convention(num_globals: usize) -> Convention {
    Convention {
        live_values: (0..num_globals).map(|g| Variable::Global(Global(g))).collect(),
        slots_used: 0,
    }
}

/** Code to be run on entry and exit from a `Machine`. */
#[derive(Debug, Clone)]
pub struct Marshal {
    /** Code to be run on entry, starting with only [`Global`]s live. */
    pub prologue: Box<[Action]>,
    /** The [`Convention`] after `prologue` and before `epilogue`. */
    pub convention: Convention,
    /** Code to be run on exit, ending with only [`Global`]s live. */
    pub epilogue: Box<[Action]>,
}

//-----------------------------------------------------------------------------

