use super::{BeetleAddress, Action, cell_bytes};
use super::super::code::{self, Action::*, BinaryOp::*};

/** A block of straight-line code. */
#[derive(Debug, Clone)]
pub struct Block {
    actions: Vec<Action>,
}

impl Block {
    pub fn new<B: AsRef<[Action]>>(block: &B) -> Self {
        Block {actions: Vec::new()}.extend(block)
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
}

impl AsRef<[Action]> for Block {
    fn as_ref(&self) -> &[Action] {
        self.actions.as_ref()
    }
}

/**
 * Execute `actions`.
 * Select the first of `cases` whose `test` (applied to `register`) passes.
 * If none pass, fall back to the trap handler.
 */
#[derive(Debug, Clone)]
pub struct State {
    actions: Vec<Action>,
    register: code::R,
    cases: Vec<Case>,
}

impl State {
    /** Constructs a State, initially with no `cases`. */
    pub fn new(block: Block, register: code::R) -> Self {
        let actions = block.actions;
        let cases = Vec::new();
        State {actions, register, cases}
    }

    /** Append `case` to `self.cases`. */
    pub fn add_case(
        &mut self,
        test: code::TestOp,
        block: Block,
        target: Option<State>,
    ) {
        let actions = block.actions;
        self.cases.push(Case {test, actions, target});
    }
}

/**
 * If `test` passes, execute `actions` then go to `target`.
 * A `target` of `None` means the root State.
 */
#[derive(Debug, Clone)]
pub struct Case {
    test: code::TestOp,
    actions: Vec<Action>,
    target: Option<State>,
}
