use std::fmt::{self, Debug, Formatter};
use std::hash::{Hash};

pub use crate::util::{AsUsize};

array_index! {
    /// Names an allocatable register. The mapping of [`Register`]s onto CPU
    /// registers is an implementation detail of a [`Target`], which may also
    /// reserve a few CPU registers for special purposes.
    ///
    /// Mijit guarantees a minimum set of [`REGISTERS`]. More are available
    /// non-portably: for example, by invoking the optimizer passing a
    /// particular [`Target`].
    ///
    /// [`Target`]: crate::target::Target
    #[derive(Copy, Clone, PartialEq, Eq, Hash)]
    pub struct Register(std::num::NonZeroU8) {
        debug_name: "Register",
        UInt: u8,
    }
}

/// Some [`Register`]s that are guaranteed to exist on all targets.
pub const REGISTERS: [Register; 12] = unsafe {[
    Register::new_unchecked(0), Register::new_unchecked(1),
    Register::new_unchecked(2), Register::new_unchecked(3),
    Register::new_unchecked(4), Register::new_unchecked(5),
    Register::new_unchecked(6), Register::new_unchecked(7),
    Register::new_unchecked(8), Register::new_unchecked(9),
    Register::new_unchecked(10), Register::new_unchecked(11),
]};

/// An alias for [`REGISTERS`]`[0]`.
pub const GLOBAL: Register = REGISTERS[0];

/// A stack-allocated spill slot.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Slot(pub usize);

impl Debug for Slot {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "Slot({})", self.0)
    }
}

/// A [`Register`] or [`Slot`].
/// Used for source operands of Mijit instructions.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Variable {
    Register(Register),
    Slot(Slot),
}

impl Debug for Variable {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(&match self {
            Variable::Register(r) => format!("{:#?}", r),
            Variable::Slot(s) => format!("{:#?}", s),
        })
    }
}

impl From<Register> for Variable {
    fn from(v: Register) -> Self {
        Variable::Register(v)
    }
}

impl From<Slot> for Variable {
    fn from(v: Slot) -> Self {
        Variable::Slot(v)
    }
}

impl TryFrom<Variable> for Register {    type Error = Variable;
    fn try_from(v: Variable) -> Result<Self, Self::Error> {
        if let Variable::Register(r) = v { Ok(r) } else { Err(v) }
    }
}

impl TryFrom<Variable> for Slot {
    type Error = Variable;
    fn try_from(v: Variable) -> Result<Self, Self::Error> {
        if let Variable::Slot(s) = v { Ok(s) } else { Err(v) }
    }
}

/// `impl IntoVariable` is useful as the type of function arguments. It accepts
/// [`Register`]s, [`Slot`]s and [`Variable`]s.
pub trait IntoVariable: Copy + Into<Variable> {}

impl<T: Copy + Into<Variable>> IntoVariable for T {}
