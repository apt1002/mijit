use std::rc::{Rc};

use super::{BeetleAddress, Action, cell_bytes};
use super::super::code::{self, Action::*, BinaryOp::*};

/** A block of straight-line code. */
#[derive(Debug, Clone)]
pub struct Block {
    test: code::TestOp,
    actions: Vec<Action>,
}

impl Block {
    pub fn new<B: AsRef<[Action]>>(test: code::TestOp, block: &B) -> Self {
        Block {
            test: test,
            actions: Vec::new(),
        }.extend(block)
    }

    pub fn append(mut self, a: Action) -> Self {
        self.actions.push(a);
        self
    }

    pub fn extend<B: AsRef<[Action]>>(mut self, block: &B) -> Self {
        self.actions.extend(block.as_ref().iter().cloned());
        self
    }

    /** Load `r` from `sp` and increment `sp`. Corrupts `temp`. */
    pub fn pop(self, sp: code::R, r: code::R, temp: code::R) -> Self {
        self.extend(&[
            Load(r, BeetleAddress::Memory(sp)),
            Constant(temp, cell_bytes(1)),
            Binary(Add, sp, sp, temp),
        ])
    }

    /** Decrement `sp` and store `r` at `sp`. Corrupts `temp`. */
    pub fn push(self, sp: code::R, r: code::R, temp: code::R) -> Self {
        self.extend(&[
            Constant(temp, cell_bytes(1)),
            Binary(Sub, sp, sp, temp),
            Store(r, BeetleAddress::Memory(sp)),
        ])
    }

    /** Finalize this Block. */
    pub fn to_case(self, cases: Option<&Rc<[Case]>>) -> Case {
        Case {
            test: self.test,
            actions: self.actions,
            cases: cases.cloned(),
        }
    }
}

impl AsRef<[Action]> for Block {
    fn as_ref(&self) -> &[Action] {
        self.actions.as_ref()
    }
}

/**
 * If `test` passes, execute `actions` then if `cases` is `None`, go to the
 * root State; otherwise, try each of `cases` in turn and if none passes,
 * fall back to the trap handler.
 */
#[derive(Debug, Clone)]
pub struct Case {
    test: code::TestOp,
    actions: Vec<Action>,
    cases: Option<Rc<[Case]>>,
}
