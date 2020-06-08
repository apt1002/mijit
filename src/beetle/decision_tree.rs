use std::num::{Wrapping};
use std::iter::{IntoIterator, FromIterator};

use super::BeetleAddress;
use super::super::code::{
    self, Width, TestOp,
    Action::*, UnaryOp::*, BinaryOp::*, DivisionOp::*,
};
use super::super::x86_64::{A as R0, D as R1, C as R2, B as R3, BP as R4};
use BeetleAddress::{Ep, A, Sp, Rp, Memory};

/** Computes the number of bytes in `n` words. */
const fn cell_bytes(n: u32) -> Wrapping<u32> { Wrapping(4 * n) }

/** The number of bits in a word. */
const CELL_BITS: Wrapping<u32> = cell_bytes(8);

type Action = code::Action<BeetleAddress>;

/** A block of straight-line code. */
#[derive(Debug, Clone)]
pub struct Block {
    actions: Vec<Action>,
}

impl Block {
    pub fn new() -> Self {
        Block {actions: Vec::new()}
    }

    pub fn append(mut self, a: Action) -> Self {
        self.actions.push(a);
        self
    }

    pub fn extend<B: AsRef<[Action]>>(mut self, block: B) -> Self {
        self.actions.extend(b.iter().cloned());
        self
    }

    /** Load `r` from `sp` and increment `sp`. */
    pub fn pop(self, sp: code::R, r: code::R) -> Self {
        self
            .append(Load(r, BeetleAddress::Memory(sp)))
            .append(Constant(R2, cell_bytes(1)))
            .append(Binary(Add, R0, R0, R2))
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
        State {
            actions: Vec::from_iter(&block),
            register: register,
            cases: Vec::new(),
        }
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

impl Case {
    pub fn new(
    ) -> Self {
    }
}
