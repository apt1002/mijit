use super::{code, target, optimizer};
use code::{Variable};

mod engine;

mod machine;
pub use machine::{Jit};

#[cfg(test)]
pub mod factorial;

/**
 * Represents the convention by which code passes values to a label. The
 * concept is similar to a calling convention, but it's for a jump, not a call.
 *
 * This is a place-holder. Possible future uses:
 *  - Register and spill-slot allocation, including dead values.
 *  - Knowledge about values, e.g. minimum and maximum possible value, and
 *    which bits are known to be set or clear.
 *  - Knowledge about possible common sub-expressions, e.g. knowing that some
 *    value is the difference of two other values.
 *  - Knowledge about the cache state, e.g. that some value is the value of
 *    some memory location, and whether it needs to be stored.
 */
#[derive(Debug, Clone)]
pub struct Convention {
    /** The [`Variable`] that will be tested next. */
    // pub discriminant: Variable,
    /** The values that are live on entry, including `discriminant`. */
    pub live_values: Vec<Variable>,
    /**
     * The number of spill [`Slot`]s used by the Convention.
     *
     * [`Slot`]: code::Slot
     */
    pub slots_used: usize,
}
