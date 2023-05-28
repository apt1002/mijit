//! Mijit's instruction set. This instruction set is used to define virtual
//! machines, and it is also used to remember what code Mijit has generated.
//!
//! ## Control-flow
//!
//! A virtual machine's control flow is restricted to a finite state machine.
//! States are defined using [`Jit::new_entry`] and transitions using
//! [`Jit::define`]. The latter takes an [`EBB`], which consists of
//! branch-free [`Action`]s and multi-way [`Switch`]es. More complex control
//! flow can be achieved by driving the finite state machine using values
//! loaded from memory.
//!
//! States defined by `new_entry` are possible entry points into the virtual
//! machine. States whose behaviour is not `define`d are also exit points.
//! Each state has a [`Marshal`] which specifies code to be executed on entry
//! and exit from the virtual machine.
//!
//! ## Storage
//!
//! A virtual machine's storage consists of a number of 64-bit [`Variable`]s.
//! There are two kinds of `Variable`:
//! - `Slot` - a value stored on the stack. `Slot`s are created by [`Push`] and
//!   destroyed by [`Drop`].
//! - `Register` - a value in a machine register.
//!
//! More complex data structures can be achieved by loading and storing
//! values in memory. On entry and exit a pointer can be passed between the
//! virtual machine and its caller. Other storage can be reached from that.
//!
//! ## Memory model
//!
//! Mijit code obeys a programming discipline in which memory locations can be
//! *shared* and can be *mutable* but cannot be both. I will abbreviate
//! "shared NAND mutable" to "shnam".
//!
//! Most programming languages that allow mutation do not enforce the shnam
//! discipline ("are not shnam"). In Java, C and Python, for example, you can
//! store a value to `x.f` and load the same value back from `y.f`, if `x` and
//! `y` are names for the same object.
//!
//! In Mijit code, storing via `x` and then loading back via `y` is undefined
//! behaviour. Mijit assumes that `x` and `y` are different objects and may
//! reorder memory accesses via `x` relative to those via `y`. Intuitively,
//! each pointer has read- and write-access capabilities associated with it,
//! and Mijit assumes that nothing writeable by one pointer is readable or
//! writeable by another.
//!
//! A new pointer is often computed from an old pointer, e.g. by adding an
//! offset or loading from memory. In this case the capabilities of the new
//! pointer are carved out of those of the old pointer.
//!
//! The [`Send`] instruction does the opposite; it merges the capabilities of
//! one pointer into those of another. Use it to warn Mijit that a store via
//! one pointer might be to the same location as a load or store via another
//! pointer.
//!
//! ## Conventions
//!
//! Instructions have at most one destination and at most two sources.
//!
//! Sources of an instruction can be any [`Variable`], but destinations are
//! always [`Register`]s. The only exception is [`Move`] which can move a value
//! into any `Variable`.
//!
//! Arithmetic operations are 32-bit or 64-bit. 32-bit operations set the upper
//! 32 bits of the destination register to zero.
//!
//! Booleans results are returned as `0` or `-1`.
//!
//! [`Move`]: Action::Move
//! [`Push`]: Action::Push
//! [`Drop`]: Action::Drop
//! [`Send`]: Action::Send
//! [`Jit::new_entry`]: crate::jit::Jit::new_entry
//! [`Jit::define`]: crate::jit::Jit::define

use std::fmt::{Debug};

mod variable;
pub use variable::{Register, REGISTERS, GLOBAL, Slot, Variable, IntoVariable};

mod enums;
pub use enums::{Precision, UnaryOp, BinaryOp, Width};

mod action;
pub use action::{Address, Action, debug_word};

mod ebb;
pub use ebb::{Switch, EBB, Ending};

pub mod builder;
pub use builder::{Builder, build, build_block};

//-----------------------------------------------------------------------------

/// Code to be run on entry and exit from a [`Jit`].
/// This effectively defines the live values at the entry/exit point, and how
/// to save and restore them.
///
/// [`Jit`]: crate::jit::Jit
#[derive(Debug, Clone)]
pub struct Marshal {
    /// Code to be run on entry, starting with only [`Register`]`[0]` live.
    pub prologue: Box<[Action]>,
    /// Code to be run on exit, ending with only [`Register`]`[0]` live.
    pub epilogue: Box<[Action]>,
}
