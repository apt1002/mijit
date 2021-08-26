/*!
 * Mijit's instruction set. This instruction set is used to define virtual
 * machines, and it is also used to remember what code Mijit has generated.
 *
 * A virtual machine's control flow is restricted to a finite state machine,
 * defined by implementing trait [`Machine`]. All the other instructions are
 * branch-free. More complex control flow can be achieved by driving the finite
 * state machine using values loaded from memory.
 *
 * A virtual machine's storage consists of a number of `Variable`s, some of
 * which are global, meaning that their values are preserved when a trap
 * occurs. More complex data structures can be achieved by loading and storing
 * values in memory.
 *
 * Arithmetic operations are 32-bit or 64-bit. 32-bit operations set the upper
 * 32 bits of the destination register to zero.
 *
 * Booleans results are returned as `0` or `-1`.
 */

use std::fmt::{Debug};
use std::hash::{Hash};

mod variable;
pub use variable::{Register, REGISTERS, Global, Slot, Variable, IntoVariable, FAST_VARIABLES};

mod switch;
pub use switch::{Case, Switch};

// Not currently used. Planned for #11.
pub mod clock;

//-----------------------------------------------------------------------------

/**
 * Represents the precision of an arithmetic operation.
 * With `P32`, the arithmetic is performed with 32-bit precision, and written
 * into the bottom 32 bits of the destination. The top 32 bits are 0.
 */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Precision {
    P32 = 0,
    P64 = 1,
}

impl Precision {
    pub fn bits(self) -> usize { 32 << (self as usize) }
}

//-----------------------------------------------------------------------------

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
    pub live_values: Vec<Variable>,
    /** The number of spill [`Slot`]s used by the `Convention`. */
    pub slots_used: usize,
}

//-----------------------------------------------------------------------------

/** Unary arithmetic operations. */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum UnaryOp {
    Abs,
    Negate,
    Not,
    // TODO: Uxt, Sxt (#12).
}

/** Binary arithmetic operations. */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Lsl,
    Lsr,
    Asr,
    And,
    Or,
    Xor,
    Lt,
    Ult,
    Eq,
    Max, // TODO: Unsigned too?
    Min, // TODO: Unsigned too?
}

/** The number of bytes transferred by a memory access. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(u8)]
pub enum Width {
    One = 0,
    Two = 1,
    Four = 2,
    Eight = 3,
}

//-----------------------------------------------------------------------------

/**
 * Indicates which parts of memory overlap with each other. More precisely,
 * indicates whether the value loaded from one address can be affected by a
 * store to another address.
 *
 * Every [`Action::Load`] and [`Action::Store`] instruction is annotated with
 * an `AliasMask`, which is internally a bitmask. If the `AliasMask`s of two
 * memory accesses have any set bits in common, and one of them is a `Store`,
 * and if the optmizer cannot prove that they access different addresses, then
 * the optimizer will not reorder the two instructions.
 *
 * It is allowed, but unhelpful, for every `AliasMask` to have all bits set.
 * This will force all memory accesses to occur in the order they are written.
 *
 * If all stores to some address precede all loads from it, then it is
 * encouraged to give all those memory accesses an `AliasMask` of zero.
 */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct AliasMask(pub u32);

impl AliasMask {
    /** Tests whether `self` and `other` have any bits in common. */
    pub fn can_alias(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

impl std::ops::BitAnd for AliasMask {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        AliasMask(self.0 & rhs.0)
    }
}

impl std::ops::BitOr for AliasMask {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        AliasMask(self.0 | rhs.0)
    }
}

impl std::ops::BitXor for AliasMask {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        AliasMask(self.0 ^ rhs.0)
    }
}

//-----------------------------------------------------------------------------

/** Called by [`Action::Debug`]. */
#[no_mangle]
pub extern fn debug_word(x: u64) {
    println!("Debug: {:#018x}", x);
}

/**
 * An imperative instruction.
 * The destination register (where applicable) is on the left.
 */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Action {
    /// dest <- src
    Move(Variable, Variable),
    /// dest <- constant
    Constant(Precision, Register, i64),
    /// dest <- op(src)
    Unary(UnaryOp, Precision, Register, Variable),
    /// dest <- op(src1, src2)
    Binary(BinaryOp, Precision, Register, Variable, Variable),
    /// dest <- \[addr]
    Load(Register, (Variable, Width), AliasMask),
    /// dest <- addr; \[addr] <- \[src]
    /// `dest` exists to make the optimizer allocate a temporary register.
    Store(Register, Variable, (Variable, Width), AliasMask),
    /// sp <- sp - 16; \[sp] <- src1; \[sp + 8] <- src2
    /// If either `src` is `None`, push a dead value.
    Push(Option<Variable>, Option<Variable>),
    /// dest1 <- \[sp]; dest2 <- \[sp + 8]; sp <- sp + 16
    /// If either `dest` is `None`, pop a dead value.
    Pop(Option<Register>, Option<Register>),
    /// sp <- sp + 16*n
    DropMany(usize),
    /// Pass `src` to [`debug_word()`].
    Debug(Variable),
}

pub trait Machine: Debug {
    /** A state of the finite state machine. */
    type State: Debug + Clone + Hash + Eq;

    /** The number of [`Global`]s used by this Machine. */
    fn num_globals(&self) -> usize;

    /**
     * The number of [`Slot`]s that exist on entry and exit from every
     * [`State`].
     */
    fn num_slots(&self) -> usize;

    /**
     * Returns a bitmask indicating which [`Variable`]s are live in `state`.
     *
     * The bits correspond to members of [`FAST_VARIABLES`].
     */
    fn liveness_mask(&self, state: Self::State) -> u64;

    /**
     * Returns code to marshal data from the [`Global`]s to the live values.
     * It is not passed anything on entry. On exit it must have initialised
     * all [`Variable`]s that are live in any [`State`].
     */
    fn prologue(&self) -> Vec<Action>;

    /**
     * Returns code to marshal data from the live values back to the
     * [`Global`]s.
     *
     * On entry, it gets all [`Variable`]s that are live in any [`State`];
     * those that are dead are set to a dummy value (`0xdeaddeaddeaddead`).
     * On exit only the `Global`s are live.
     */
    fn epilogue(&self) -> Vec<Action>;

    /**
     * Defines the transitions of the finite state machine.
     *  - state - the source State.
     * Returns a [`Case`] for each transition from `state`.
     */
    fn code(&self, state: Self::State) -> Switch<Case<Self::State>>;

    /** Returns some States from which all others are reachable. */
    fn initial_states(&self) -> Vec<Self::State>;
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::collections::{HashMap};

    /**
     * An emulator for a subset of Mijit code, useful for testing
     * automatically-generated code.
     */
    pub struct Emulator {
        variables: Vec<Variable>,
    }

    impl Emulator {
        pub fn new(variables: Vec<Variable>) -> Self {
            Emulator {variables}
        }

        pub fn execute(&self, actions: &[Action]) -> HashMap<Variable, i64> {
            let mut state: HashMap<Variable, i64> = self.variables.iter().enumerate().map(|(i, v)| {
                (*v, 1000 + i as i64)
            }).collect();
            for action in actions {
                match action {
                    &Action::Move(dest, src) => {
                        let x = *state.get(&src).expect("Missing from state");
                        state.insert(dest, x);
                    },
                    &Action::Constant(Precision::P64, dest, imm) => {
                        state.insert(dest.into(), imm);
                    },
                    &Action::Unary(UnaryOp::Not, Precision::P64, dest, src) => {
                        let x = *state.get(&src).expect("Missing from state");
                        state.insert(dest.into(), !x);
                    },
                    &Action::Binary(BinaryOp::Add, Precision::P64, dest, src1, src2) => {
                        let x = *state.get(&src1).expect("Missing from state");
                        let y = *state.get(&src2).expect("Missing from state");
                        state.insert(dest.into(), x + y);
                    },
                    _ => panic!("Don't know how to execute {:#?}", action),
                }
            }
            state
        }
    }

    /** Ensure the linker symbol `debug_word` is included in the binary. */
    #[test]
    fn not_really_a_test() {
        debug_word(0);
    }
}
