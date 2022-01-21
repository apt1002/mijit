use super::{code, target};

mod engine;
use engine::{Engine, CaseId};

mod entry;
pub use entry::{Jit2, EntryId};

mod machine;
pub use machine::{Jit};

#[cfg(test)]
pub mod factorial;
