use std::convert::{TryFrom};
use std::fmt::{self, Debug, Formatter};
use std::hash::{Hash};

pub use crate::util::{AsUsize};

array_index! {
    /**
     * Names an allocatable register. The mapping of [`Register`]s onto CPU
     * registers is an implementation detail of a [`Target`], which may also
     * reserve a few CPU registers for special purposes.
     *
     * Mijit guarantees a minimum set of [`REGISTERS`]. More are available
     * non-portably: for example, by invoking the optimizer passing a
     * particular [`Target`].
     *
     * [`Target`]: super::target::Target
     */
    #[derive(Copy, Clone, PartialEq, Eq, Hash)]
    pub struct Register(std::num::NonZeroU8) {
        debug_name: "Register",
        UInt: u8,
    }
}

/** Some [`Register`]s that are guaranteed to exist on all targets. */
pub const REGISTERS: [Register; 12] = unsafe {[
    Register::new_unchecked(0), Register::new_unchecked(1),
    Register::new_unchecked(2), Register::new_unchecked(3),
    Register::new_unchecked(4), Register::new_unchecked(5),
    Register::new_unchecked(6), Register::new_unchecked(7),
    Register::new_unchecked(8), Register::new_unchecked(9),
    Register::new_unchecked(10), Register::new_unchecked(11),
]};

/** Names a value that persists when Mijit is not running. */
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Global(pub usize);

impl Debug for Global {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "Global({})", self.0)
    }
}

/** A stack-allocated spill slot. */
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Slot(pub usize);

impl Debug for Slot {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "Slot({})", self.0)
    }
}

/** A spill slot or register. */
// TODO: Reorder cases for consistency: Register, Global, Slot.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Variable {
    Global(Global),
    Slot(Slot),
    Register(Register),
}

impl Debug for Variable {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(&match self {
            Variable::Global(g) => format!("{:#?}", g),
            Variable::Slot(s) => format!("{:#?}", s),
            Variable::Register(r) => format!("{:#?}", r),
        })
    }
}

impl From<Global> for Variable {
    fn from(v: Global) -> Self {
        Variable::Global(v)
    }
}

impl From<Slot> for Variable {
    fn from(v: Slot) -> Self {
        Variable::Slot(v)
    }
}

impl From<Register> for Variable {
    fn from(v: Register) -> Self {
        Variable::Register(v)
    }
}

impl TryFrom<Variable> for Global {
    type Error = Variable;
    fn try_from(v: Variable) -> Result<Self, Self::Error> {
        if let Variable::Global(g) = v { Ok(g) } else { Err(v) }
    }
}

impl TryFrom<Variable> for Slot {
    type Error = Variable;
    fn try_from(v: Variable) -> Result<Self, Self::Error> {
        if let Variable::Slot(s) = v { Ok(s) } else { Err(v) }
    }
}

impl TryFrom<Variable> for Register {
    type Error = Variable;
    fn try_from(v: Variable) -> Result<Self, Self::Error> {
        if let Variable::Register(r) = v { Ok(r) } else { Err(v) }
    }
}

/**
 * `impl IntoVariable` is useful as the type of function arguments. It accepts
 * both [`Register`]s and [`Variable`]s.
 */
pub trait IntoVariable: Copy + Into<Variable> {}

impl<T: Copy + Into<Variable>> IntoVariable for T {}

const fn make_reg(r: usize) -> Variable { Variable::Register(REGISTERS[r]) }
const fn make_slot(s: usize) -> Variable { Variable::Slot(Slot(s)) }

/**
 * [`Variable`]s that are likely to be efficient to access on all [`Target`]s.
 * The first 12 are guaranteed to match `REGISTERS`.
 *
 * [`Target`]: super::target::Target
 */
pub const FAST_VARIABLES: [Variable; 64] = [
    make_reg(0), make_reg(1), make_reg(2), make_reg(3),
    make_reg(4), make_reg(5), make_reg(6), make_reg(7),
    make_reg(8), make_reg(9), make_reg(10), make_reg(11),
    make_slot(0), make_slot(1), make_slot(2), make_slot(3),
    make_slot(4), make_slot(5), make_slot(6), make_slot(7),
    make_slot(8), make_slot(9), make_slot(10), make_slot(11),
    make_slot(12), make_slot(13), make_slot(14), make_slot(15),
    make_slot(16), make_slot(17), make_slot(18), make_slot(19),
    make_slot(20), make_slot(21), make_slot(22), make_slot(23),
    make_slot(24), make_slot(25), make_slot(26), make_slot(27),
    make_slot(28), make_slot(29), make_slot(30), make_slot(31),
    make_slot(32), make_slot(33), make_slot(34), make_slot(35),
    make_slot(36), make_slot(37), make_slot(38), make_slot(39),
    make_slot(40), make_slot(41), make_slot(42), make_slot(43),
    make_slot(44), make_slot(45), make_slot(46), make_slot(47),
    make_slot(48), make_slot(49), make_slot(50), make_slot(51),
];
