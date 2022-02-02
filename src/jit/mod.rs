use super::{code, target};

mod engine;
use engine::{Engine, CaseId};

mod entry;
pub use entry::{Jit, EntryId};

#[cfg(test)]
pub mod factorial;
