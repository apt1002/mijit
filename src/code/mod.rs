//! Mijit's instruction set. This instruction set is used to define virtual
//! machines, and it is also used to remember what code Mijit has generated.
//! 
//! A virtual machine's control flow is restricted to a finite state machine.
//! States are defined using [`jit::Jit::new_entry`] and transitions using
//! [`jit::Jit::define`]. The latter takes an [`EBB`], which consists of
//! branch-free [`Action`]s and multi-way [`Switch`]es. More complex control
//! flow can be achieved by driving the finite state machine using values
//! loaded from memory.
//! 
//! A virtual machine's storage consists of a number of `Variable`s, some of
//! which are global, meaning that their values are preserved when a trap
//! occurs. More complex data structures can be achieved by loading and storing
//! values in memory.
//! 
//! Arithmetic operations are 32-bit or 64-bit. 32-bit operations set the upper
//! 32 bits of the destination register to zero.
//! 
//! Booleans results are returned as `0` or `-1`.

use std::fmt::{Debug};

mod variable;
pub use variable::{Register, REGISTERS, Global, Slot, Variable, IntoVariable};

mod enums;
pub use enums::{Precision, UnaryOp, BinaryOp, Width, AliasMask};

mod action;
pub use action::{Action, debug_word};

mod ebb;
pub use ebb::{Switch, EBB, Ending};

mod convention;
pub use convention::{Convention, Propagator};

pub mod builder;

//-----------------------------------------------------------------------------

/// Code to be run on entry and exit from a `Jit`.
#[derive(Debug, Clone)]
pub struct Marshal {
    /// Code to be run on entry, starting with only [`Global`]s live.
    pub prologue: Box<[Action]>,
    /// Code to be run on exit, ending with only [`Global`]s live.
    pub epilogue: Box<[Action]>,
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    pub use action::tests::{Emulator};
    pub use ebb::tests::{random_ebb, random_ebb_convention};
}
