use super::{buffer, code};

mod pool;
pub use pool::{Word, Pool};

mod label;
pub use label::{Patch, Label};

mod traits;
pub use traits::{Lower, ExecuteFn, Execute, Target};

pub mod x86_64;

/**
 * The [`Register`] which holds the state index on entry and exit from Mijit.
 */
// TODO: Somehow hide the state index from this module, and delete this.
pub const STATE_INDEX: code::Register = code::REGISTERS[0];

//-----------------------------------------------------------------------------


/** A [`Target`] that generates code which can be executed. */
pub fn native() -> impl Target {
    x86_64::Target
}
