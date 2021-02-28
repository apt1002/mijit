/*!
 * Mijit's instruction set. This instruction set is used to define virtual
 * machines, and it is also used to remember what code Mijit has generated.
 *
 * A virtual machine's control flow is restricted to a finite state machine,
 * defined by implementing trait [`Machine`]. All the other instructions are
 * branch-free. More complex control flow can be achieved by driving the finite
 * state machine using values loaded from memory.
 *
 * A virtual machine's storage consists of a number of `Value`s, some of which
 * are global, meaning that their values are preserved when a trap occurs. More
 * complex data structures can be achieved by loading and storing values in
 * memory.
 *
 * Arithmetic operations are 32-bit or 64-bit. 32-bit operations set the upper
 * 32 bits of the destination register to zero.
 *
 * Booleans results are returned as `0` or `-1`.
 */

use std::fmt::{self, Debug};
use std::hash::{Hash};

pub use super::x86_64::{Register, Precision};

// Not currently used. Planned for #11.
pub mod clock;

/** A spill slot or register. */
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Slot(usize),
    Register(Register),
}

impl Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(&match self {
            Value::Slot(n) => format!("Slot({})", n),
            Value::Register(r) => format!("{:#?}", r),
        })
    }
}

impl From<Register> for Value {
    fn from(v: Register) -> Self {
        Value::Register(v)
    }
}

/** Guard conditions used to define control flow. */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TestOp {
    // TODO: These constants should probably be 64-bit.
    Bits(Value, i32, i32),
    Lt(Value, i32),
    Ge(Value, i32),
    Ult(Value, i32),
    Uge(Value, i32),
    Eq(Value, i32),
    Ne(Value, i32),
    Always,
}

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

/** Division operations. */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum DivisionOp {
    SignedDivMod,
    UnsignedDivMod,
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

/**
 * Indicates which parts of memory overlap with each other. More precisely,
 * indicates whether the value loaded from one address can be affected by a
 * store to another address.
 *
 * Every [`Action::Load`] and [`Action::Store`] instruction is annotated with
 * an AliasMask, which is internally a bitmask. If the AliasMasks of two
 * memory accesses have any set bits in common, and one of them is a `Store`,
 * and if the optmizer cannot prove that they access different addresses, then
 * the optimizer will not reorder the two instructions.
 *
 * It is allowed, but unhelpful, for every AliasMask to have all bits set.
 * This will force all memory accesses to occur in the order they are written.
 *
 * If all stores to some address precede all loads from it, then it is
 * encouraged to give all those memory accesses an AliasMask of zero.
 */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct AliasMask(pub u32);

impl AliasMask {
    /** Tests whether `self` and `other` have any bits in common. */
    pub fn can_alias(&self, other: &Self) -> bool {
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

/**
 * An imperative instruction.
 * The destination register (where applicable) is on the left.
 */
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Action {
    Constant(Precision, Value, i64),
    Move(Value, Value),
    Unary(UnaryOp, Precision, Value, Value),
    Binary(BinaryOp, Precision, Register, Value, Value),
    Division(DivisionOp, Precision, Value, Value, Value, Value),
    Load(Value, (Value, Width), AliasMask),
    Store(Value, (Value, Width), AliasMask),
    Push(Value),
    Pop(Value),
    Debug(Value),
}

pub trait Machine: Debug {
    /** A state of the finite state machine. */
    type State: Debug + Clone + Hash + Eq;

    /** The number of spill slots reserved for the Machine's globals. */
    fn num_globals(&self) -> usize;

    /**
     * Defines the transitions of the finite state machine.
     *  - state - the source State.
     * Returns a (condition, actions, new_state) for each transition from
     * `state`:
     *  - condition - when to use the transition. Mijit selects the first
     *    transition with a true condition.
     *  - actions - code to execute when the transition is selected.
     *  - new_state - the destination State.
     */
    fn get_code(&self, state: Self::State) ->
        Vec<(
            (TestOp, Precision),
            Vec<Action>,
            Self::State,
        )>;

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
        values: Vec<Value>,
    }

    impl Emulator {
        pub fn new(values: Vec<Value>) -> Self {
            Emulator {values}
        }

        pub fn execute(&self, actions: &[Action]) -> HashMap<Value, i64> {
            let mut state: HashMap<Value, i64> = self.values.iter().enumerate().map(|(i, value)| {
                (value.clone(), 1000 + i as i64)
            }).collect();
            for action in actions {
                match action {
                    &Action::Constant(Precision::P64, dest, imm) => {
                        state.insert(dest, imm);
                    },
                    &Action::Move(dest, src) => {
                        let x = *state.get(&src).expect("Missing from state");
                        state.insert(dest, x);
                    },
                    &Action::Unary(UnaryOp::Not, Precision::P64, dest, src) => {
                        let x = *state.get(&src).expect("Missing from state");
                        state.insert(dest, !x);
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
}
