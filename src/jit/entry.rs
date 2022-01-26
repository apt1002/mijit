use crate::util::{AsUsize};
use super::{code, Engine, CaseId};
use super::target::{Label, Word, Target};
use code::{Global, Marshal, EBB};

// EntryId.
array_index! {
    /** Identifies an entry point of an [`Engine`]. */
    #[derive(Copy, Clone, Hash, PartialEq, Eq)]
    pub struct EntryId(std::num::NonZeroUsize) {
        debug_name: "EntryId",
        UInt: usize,
    }
}

/** An entry point into the compiled code. */
#[derive(Debug)]
struct Entry {
    label: Label,
    case: CaseId,
    is_defined: bool,
}

//-----------------------------------------------------------------------------

pub struct Jit2<T: Target> {
    engine: Engine<T>,
    /** Indexed by `EntryId`. */
    entries: Vec<Entry>,
}

// Use a macro, not a method, to keep the borrow-checker happy.
macro_rules! get {
    ($self: expr, $id: expr) => ($self.entries[$id.as_usize()])
}

impl<T: Target> Jit2<T> {
    pub fn new(target: T, num_globals: usize) -> Self {
        Self {
            engine: Engine::new(target, num_globals),
            entries: Vec::new(),
        }
    }

    /** Borrows the value of variable `global`. */
    pub fn global_mut(&mut self, global: Global) -> &mut Word {
        self.engine.global_mut(global)
    }

    /**
     * Constructs a new entry/exit point. Initially, the code at the entry
     * point will immediately exit, returning `exit_value`. Use `define()` to
     * change its behaviour.
     *
     *  - exit_value - `run()` will return this value to its caller if
     *    execution ends at this entry/exit point. Must be non-negative.
     */
    // TODO: Document `marshal` and `exit_value`.
    pub fn new_entry(&mut self, marshal: &Marshal, exit_value: i64) -> EntryId {
        let (label, case) = self.engine.new_entry(marshal, exit_value);
        let id = EntryId::new(self.entries.len()).unwrap();
        self.entries.push(Entry {label, case, is_defined: false});
        id
    }

    /**
     * Replace the code at `entry`. Each `EntryId` may only be defined once.
     *
     *  - entry - the entry point to modify.
     *  - ebb - the extended basic block defining the desired behaviour.
     */
    pub fn define(&mut self, entry: EntryId, ebb: &EBB<EntryId>) {
        assert!(!get!(self, entry).is_defined);
        self.engine.build(get!(self, entry).case, ebb, &|e| get!(self, e).case);
        get!(self, entry).is_defined = true;
    }

    /**
     * Call the compiled code starting at `entry`.
     *
     * # Safety
     *
     * This will crash if the code is compiled for the wrong [`Target`] or if
     * the code is invalid.
     */
    pub unsafe fn run(mut self, entry: EntryId) -> std::io::Result<(Self, Word)> {
        let label = &get!(self, entry).label;
        let (engine, ret) = self.engine.run(label)?;
        self.engine = engine;
        Ok((self, ret))
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::super::target::{native};

    use super::super::factorial::*;

    #[test]
    pub fn factorial() {
        let jit = Factorial::new(native());
        let (_, result) = jit.run(5).expect("Execute failed");
        assert_eq!(result, 120);
    }
}
