use super::{code, graph, target, optimizer};

mod engine;
use engine::{Engine, CaseId};

mod entry;
pub use entry::{Jit, EntryId};

// #[cfg(test)]
// pub mod factorial;
