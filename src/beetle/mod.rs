use std::num::{Wrapping};

use super::{control_flow};
use super::code::{
    self, Width,
    Action::*, UnaryOp::*, BinaryOp::*, DivisionOp::*, TestOp
};

/** Beetle's address space. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Address {
    EP,
    A,
    SP,
    RP,
    S0,
    R0,
    Throw,
    Bad,
    NotAddress,
    Memory0,
    Memory(code::R),
}

impl control_flow::Address for Address {
    fn can_alias(&self, other: &Self) -> bool {
        assert_ne!(self, other);
        match self {
            &Address::Memory(_) => match other {
                &Address::Memory(_) => true,
                _ => false,
            },
            _ => false,
        }
    }
}

/** Computes the number of bytes in `n` words. */
pub const fn cell_bytes(n: u32) -> u32 { Wrapping(4 * n).0 }

/** The number of bits in a word. */
pub const CELL_BITS: u32 = cell_bytes(8);

pub type Action = code::Action<Address>;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum State {
    Root,
    Dispatch,
    Next,
    Pick,
    Roll,
    Qdup,
    Lshift,
    Rshift,
    Branch,
    Branchi,
    Qbranch,
    Qbranchi,
    Loop,
    Loopi,
    Ploopp,
    Ploopm,
    Ploop,
    Ploopip,
    Ploopim,
    Ploopi,
}

#[derive(Debug)]
pub struct Machine;

impl control_flow::Machine for Machine {
    type State = State;
    type Address = Address;

    fn get_code(&self, state: Self::State) -> Vec<(code::TestOp, Vec<Action>, Self::State)> {
        use super::x86_64::Register::{RA, RD, RB, RBP, RSI};
        use Address::{EP as B_EP, A as B_A, SP as B_SP, RP as B_RP, Memory};
        match state {
            State::Root => {vec![
                (TestOp::Always, vec![
                    Load(RA, B_A),
                    Constant(RSI, 8),
                    Binary(Asr, RD, RA, RSI),
                    Store(RD, B_A),
                ], State::Dispatch),
            ]},
            State::Next => {vec![
                (TestOp::Always, vec![
                    Load(RA, B_EP), // FIXME: Add check that EP is valid.
                    Load(RD, Memory(RA)),
                    Store(RD, B_A),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_EP),
                ], State::Root),
            ]},
            State::Pick => {
                let mut pick = Vec::new();
                for u in 0..4 {
                    pick.push((
                        TestOp::Eq(RD, u),
                        vec![
                            Load(RA, B_SP),
                            Constant(RSI, cell_bytes(u + 1)),
                            Binary(Add, RD, RA, RSI),
                            Load(RD, Memory(RD)),
                            Store(RD, Memory(RA)),
                        ],
                        State::Root,
                    ));
                }
                pick
            },
            State::Roll => {
                let mut roll = Vec::new();
                for u in 0..4 {
                    let mut rollu = vec![
                        Constant(RSI, cell_bytes(u)),
                        Binary(Add, RBP, RA, RSI),
                        Load(RB, Memory(RBP)),
                    ];
                    for v in 0..u {
                        rollu.extend(vec![
                            Constant(RSI, cell_bytes(v)),
                            Binary(Add, RSI, RA, RSI),
                            Load(RD, Memory(RSI)),
                            Store(RB, Memory(RSI)),
                            Move(RB, RD),
                        ]);
                    }
                    rollu.extend(vec![
                        Store(RB, Memory(RBP)),
                    ]);
                    roll.push((
                        TestOp::Eq(RD, u),
                        rollu,
                        State::Root,
                    ));
                }
                roll
            },
            State::Qdup => {vec![
                (TestOp::Eq(RD, 0), vec![], State::Root),
                (TestOp::Ne(RD, 0), vec![
                     Constant(RSI, cell_bytes(1)),
                     Binary(Sub, RA, RA, RSI),
                     Store(RD, Memory(RA)),
                     Store(RA, B_SP),
                ], State::Root),
            ]},
            State::Lshift => {vec![
                (TestOp::Ult(RSI, CELL_BITS), vec![
                    Binary(Lsl, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                ], State::Root),
                (TestOp::Uge(RSI, CELL_BITS), vec![
                    Constant(RD, 0),
                    Store(RD, Memory(RA)),
                ], State::Root),
            ]},
            State::Rshift => {vec![
                (TestOp::Ult(RSI, CELL_BITS), vec![
                    Binary(Lsr, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                ], State::Root),
                (TestOp::Uge(RSI, CELL_BITS), vec![
                    Constant(RD, 0),
                    Store(RD, Memory(RA)),
                ], State::Root),
            ]},
            State::Branch => {vec![
                (TestOp::Always, vec![
                    // Load EP from the cell it points to.
                    Load(RA, B_EP),
                    Load(RA, Memory(RA)),
                    Store(RA, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),
            ]},
            State::Branchi => {vec![
                (TestOp::Always, vec![
                    Load(RA, B_EP),
                    Load(RD, B_A),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Mul, RD, RD, RSI),
                    Binary(Add, RA, RA, RD),
                    Store(RA, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),
            ]},
            State::Qbranch => {vec![
                (TestOp::Eq(RD, 0), vec![], State::Branch),
                (TestOp::Ne(RD, 0), vec![
                    Load(RA, B_EP),
                    Constant(RD, cell_bytes(1)),
                    Binary(Add, RA, RA, RD),
                    Store(RA, B_EP),
                ], State::Root),
            ]},
            State::Qbranchi => {vec![
                (TestOp::Eq(RD, 0), vec![], State::Branchi),
                (TestOp::Ne(RD, 0), vec![], State::Root),
            ]},
            State::Loop => {vec![
                (TestOp::Eq(RB, 0), vec![
                    // Discard the loop index and limit.
                    Load(RA, B_RP),
                    Constant(RSI, cell_bytes(2)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_RP),
                    // Add 4 to EP.
                    Load(RA, B_EP), // FIXME: Add check that EP is valid.
                    Constant(RD, cell_bytes(1)),
                    Binary(Add, RA, RA, RD),
                    Store(RA, B_EP),
                ], State::Root),
                (TestOp::Ne(RB, 0), vec![], State::Branch),
            ]},
            State::Loopi => {vec![
                (TestOp::Eq(RB, 0), vec![
                    // Discard the loop index and limit.
                    Load(RA, B_RP),
                    Constant(RSI, cell_bytes(2)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_RP),
                ], State::Root),
                (TestOp::Ne(RB, 0), vec![], State::Branchi),
            ]},
            State::Ploopp => {vec![
                (TestOp::Lt(RBP, 0), vec![
                    // Discard the loop index and limit.
                    Load(RA, B_RP),
                    Constant(RSI, cell_bytes(2)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_RP),
                    // Add 4 to EP.
                    Load(RA, B_EP), // FIXME: Add check that EP is valid.
                    Constant(RD, cell_bytes(1)),
                    Binary(Add, RA, RA, RD),
                    Store(RA, B_EP),
                ], State::Root),
                (TestOp::Ge(RBP, 0), vec![], State::Branch),
            ]},
            State::Ploopm => {vec![
                (TestOp::Lt(RBP, 0), vec![
                    // Discard the loop index and limit.
                    Load(RA, B_RP),
                    Constant(RSI, cell_bytes(2)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_RP),
                    // Add 4 to EP.
                    Load(RA, B_EP), // FIXME: Add check that EP is valid.
                    Constant(RD, cell_bytes(1)),
                    Binary(Add, RA, RA, RD),
                    Store(RA, B_EP),
                ], State::Root),
                (TestOp::Ge(RBP, 0), vec![], State::Branch),
            ]},
            State::Ploop => {vec![
                (TestOp::Ge(RD, 0), vec![
                    Unary(Not, RBP, RBP),
                    Binary(And, RBP, RBP, RB),
                ], State::Ploopp),
                (TestOp::Lt(RD, 0), vec![
                    Unary(Not, RB, RB),
                    Binary(And, RBP, RBP, RB),
                ], State::Ploopm),
            ]},
            State::Ploopip => {vec![
                (TestOp::Lt(RBP, 0), vec![
                    // Discard the loop index and limit.
                    Load(RA, B_RP),
                    Constant(RSI, cell_bytes(2)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_RP),
                ], State::Root),
                (TestOp::Ge(RBP, 0), vec![], State::Branchi),
            ]},
            State::Ploopim => {vec![
                (TestOp::Lt(RBP, 0), vec![
                    // Discard the loop index and limit.
                    Load(RA, B_RP),
                    Constant(RSI, cell_bytes(2)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_RP),
                ], State::Root),
                (TestOp::Ge(RBP, 0), vec![], State::Branchi),
            ]},
            State::Ploopi => {vec![
                (TestOp::Ge(RD, 0), vec![
                    Unary(Not, RBP, RBP),
                    Binary(And, RBP, RBP, RB),
                ], State::Ploopip),
                (TestOp::Lt(RD, 0), vec![
                    Unary(Not, RB, RB),
                    Binary(And, RBP, RBP, RB),
                ], State::Ploopim),
            ]},
            State::Dispatch => {vec![
                // NEXT
                (TestOp::Bits(RA, 0xff, 0x00), vec![], State::Next),

                // DUP
                (TestOp::Bits(RA, 0xff, 0x01), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // DROP
                (TestOp::Bits(RA, 0xff, 0x02), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                ], State::Root),

                // SWAP
                (TestOp::Bits(RA, 0xff, 0x03), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RD, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Load(RB, Memory(RD)),
                    Store(RSI, Memory(RD)),
                    Store(RB, Memory(RA)),
                ], State::Root),

                // OVER
                (TestOp::Bits(RA, 0xff, 0x04), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RD, RA, RSI),
                    Load(RB, Memory(RD)),
                    Binary(Sub, RA, RA, RSI),
                    Store(RB, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // ROT
                (TestOp::Bits(RA, 0xff, 0x05), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RBP, RA, RSI),
                    Load(RB, Memory(RBP)),
                    Store(RD, Memory(RBP)),
                    Constant(RSI, cell_bytes(2)),
                    Binary(Add, RBP, RA, RSI),
                    Load(RD, Memory(RBP)),
                    Store(RB, Memory(RBP)),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // -ROT
                (TestOp::Bits(RA, 0xff, 0x06), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(2)),
                    Binary(Add, RBP, RA, RSI),
                    Load(RB, Memory(RBP)),
                    Store(RD, Memory(RBP)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RBP, RA, RSI),
                    Load(RD, Memory(RBP)),
                    Store(RB, Memory(RBP)),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // TUCK
                (TestOp::Bits(RA, 0xff, 0x07), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RBP, RA, RSI),
                    Load(RB, Memory(RBP)),
                    Store(RD, Memory(RBP)),
                    Store(RB, Memory(RA)),
                    Binary(Sub, RA, RA, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // NIP
                (TestOp::Bits(RA, 0xff, 0x08), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // PICK
                (TestOp::Bits(RA, 0xff, 0x09), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                ], State::Pick),

                // ROLL
                (TestOp::Bits(RA, 0xff, 0x0a), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                ], State::Roll),

                // ?DUP
                (TestOp::Bits(RA, 0xff, 0x0b), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                ], State::Qdup),

                // >R
                (TestOp::Bits(RA, 0xff, 0x0c), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                    Load(RA, B_RP),
                    Binary(Sub, RA, RA, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_RP),
                ], State::Root),

                // R>
                (TestOp::Bits(RA, 0xff, 0x0d), vec![
                    Load(RA, B_RP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_RP),
                    Load(RA, B_SP),
                    Binary(Sub, RA, RA, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // R@
                (TestOp::Bits(RA, 0xff, 0x0e), vec![
                    Load(RA, B_RP),
                    Load(RD, Memory(RA)),
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // <
                (TestOp::Bits(RA, 0xff, 0x0f), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(Lt, RD, RSI, RD),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // >
                (TestOp::Bits(RA, 0xff, 0x10), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(Lt, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // =
                (TestOp::Bits(RA, 0xff, 0x11), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(Eq, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // <>
                (TestOp::Bits(RA, 0xff, 0x12), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(Eq, RD, RD, RSI),
                    Unary(Not, RD, RD),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // 0<
                (TestOp::Bits(RA, 0xff, 0x13), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, 0),
                    Binary(Lt, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // 0>
                (TestOp::Bits(RA, 0xff, 0x14), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, 0),
                    Binary(Lt, RD, RSI, RD),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // 0=
                (TestOp::Bits(RA, 0xff, 0x15), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, 0),
                    Binary(Eq, RD, RSI, RD),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // 0<>
                (TestOp::Bits(RA, 0xff, 0x16), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, 0),
                    Binary(Eq, RD, RSI, RD),
                    Unary(Not, RD, RD),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // U<
                (TestOp::Bits(RA, 0xff, 0x17), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(Ult, RD, RSI, RD),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // U>
                (TestOp::Bits(RA, 0xff, 0x18), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(Ult, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // 0
                (TestOp::Bits(RA, 0xff, 0x19), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Constant(RSI, 0),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // 1
                (TestOp::Bits(RA, 0xff, 0x1a), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Constant(RSI, 1),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // -1
                (TestOp::Bits(RA, 0xff, 0x1b), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Constant(RSI, (-Wrapping(1u32)).0),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // CELL
                (TestOp::Bits(RA, 0xff, 0x1c), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Constant(RSI, cell_bytes(1)),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // -CELL
                (TestOp::Bits(RA, 0xff, 0x1d), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Constant(RSI, (-Wrapping(cell_bytes(1))).0),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // +
                (TestOp::Bits(RA, 0xff, 0x1e), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(Add, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // -
                (TestOp::Bits(RA, 0xff, 0x1f), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(Sub, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // >-<
                (TestOp::Bits(RA, 0xff, 0x20), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(Sub, RD, RSI, RD),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // 1+
                (TestOp::Bits(RA, 0xff, 0x21), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, 1),
                    Binary(Add, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // 1-
                (TestOp::Bits(RA, 0xff, 0x22), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, 1),
                    Binary(Sub, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // CELL+
                (TestOp::Bits(RA, 0xff, 0x23), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // CELL-
                (TestOp::Bits(RA, 0xff, 0x24), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // *
                (TestOp::Bits(RA, 0xff, 0x25), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(Mul, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // /
                (TestOp::Bits(RA, 0xff, 0x26), vec![
                    // TODO
                ], State::Root),

                // MOD
                (TestOp::Bits(RA, 0xff, 0x27), vec![
                    // TODO
                ], State::Root),

                // /MOD
                (TestOp::Bits(RA, 0xff, 0x28), vec![
                    // TODO
                ], State::Root),

                // U/MOD
                (TestOp::Bits(RA, 0xff, 0x29), vec![
                    Load(RB, B_SP),
                    Load(RD, Memory(RB)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RSI, RB, RSI),
                    Load(RA, Memory(RSI)),
                    Division(UnsignedDivMod, RA, RD, RA, RD),
                    Store(RD, Memory(RSI)),
                    Store(RA, Memory(RB)),
                ], State::Root),

                // S/REM
                (TestOp::Bits(RA, 0xff, 0x2a), vec![
                    Load(RB, B_SP),
                    Load(RD, Memory(RB)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RSI, RB, RSI),
                    Load(RA, Memory(RSI)),
                    Division(SignedDivMod, RA, RD, RA, RD),
                    Store(RD, Memory(RSI)),
                    Store(RA, Memory(RB)),
                ], State::Root),

                // 2/
                (TestOp::Bits(RA, 0xff, 0x2b), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, 1),
                    Binary(Asr, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // CELLS
                (TestOp::Bits(RA, 0xff, 0x2c), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Mul, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // ABS
                (TestOp::Bits(RA, 0xff, 0x2d), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Unary(Abs, RD, RD),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // NEGATE
                (TestOp::Bits(RA, 0xff, 0x2e), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Unary(Negate, RD, RD),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // MAX
                (TestOp::Bits(RA, 0xff, 0x2f), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                    Load(RSI, Memory(RA)),
                    Binary(Max, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // MIN
                (TestOp::Bits(RA, 0xff, 0x30), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                    Load(RSI, Memory(RA)),
                    Binary(Min, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // INVERT
                (TestOp::Bits(RA, 0xff, 0x31), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Unary(Not, RD, RD),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // AND
                (TestOp::Bits(RA, 0xff, 0x32), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(And, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // OR
                (TestOp::Bits(RA, 0xff, 0x33), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(Or, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // XOR
                (TestOp::Bits(RA, 0xff, 0x34), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Binary(Xor, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // LSHIFT
                (TestOp::Bits(RA, 0xff, 0x35), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Lshift),

                // RSHIFT
                (TestOp::Bits(RA, 0xff, 0x36), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Load(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Rshift),

                // 1LSHIFT
                (TestOp::Bits(RA, 0xff, 0x37), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, 1),
                    Binary(Lsl, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // 1RSHIFT
                (TestOp::Bits(RA, 0xff, 0x38), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, 1),
                    Binary(Lsr, RD, RD, RSI),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // @
                (TestOp::Bits(RA, 0xff, 0x39), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Load(RD, Memory(RD)),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // !
                (TestOp::Bits(RA, 0xff, 0x3a), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RSI, RA, RSI),
                    Load(RB, Memory(RSI)),
                    Store(RB, Memory(RD)),
                    Constant(RSI, cell_bytes(2)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                ], State::Root),

                // C@
                (TestOp::Bits(RA, 0xff, 0x3b), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    LoadNarrow(Width::One, RD, Memory(RD)),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // C!
                (TestOp::Bits(RA, 0xff, 0x3c), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RSI, RA, RSI),
                    Load(RB, Memory(RSI)),
                    StoreNarrow(Width::One, RB, Memory(RD)),
                    Constant(RSI, cell_bytes(2)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                ], State::Root),

                // +!
                (TestOp::Bits(RA, 0xff, 0x3d), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RSI, RA, RSI),
                    Load(RB, Memory(RSI)),
                    Load(RBP, Memory(RD)),
                    Binary(Add, RB, RBP, RB),
                    Store(RB, Memory(RD)),
                    Constant(RSI, cell_bytes(2)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                ], State::Root),

                // SP@
                (TestOp::Bits(RA, 0xff, 0x3e), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RSI, RA, RSI),
                    Store(RA, Memory(RSI)),
                    Store(RSI, B_SP),
                ], State::Root),

                // SP!
                (TestOp::Bits(RA, 0xff, 0x3f), vec![
                    Load(RA, B_SP),
                    Load(RA, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // RP@
                (TestOp::Bits(RA, 0xff, 0x40), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Load(RSI, B_RP),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // RP!
                (TestOp::Bits(RA, 0xff, 0x41), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Store(RD, B_RP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                ], State::Root),

                // EP@
                (TestOp::Bits(RA, 0xff, 0x42), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Load(RSI, B_EP),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // S0@
                (TestOp::Bits(RA, 0xff, 0x43), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Load(RSI, Address::S0),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // S0!
                (TestOp::Bits(RA, 0xff, 0x44), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Store(RD, Address::S0),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                ], State::Root),

                // R0@
                (TestOp::Bits(RA, 0xff, 0x45), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Load(RSI, Address::R0),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // R0!
                (TestOp::Bits(RA, 0xff, 0x46), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Store(RD, Address::R0),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                ], State::Root),

                // 'THROW@
                (TestOp::Bits(RA, 0xff, 0x47), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Load(RSI, Address::Throw),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // 'THROW!
                (TestOp::Bits(RA, 0xff, 0x48), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Store(RD, Address::Throw),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                ], State::Root),

                // MEMORY@
                (TestOp::Bits(RA, 0xff, 0x49), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Load(RSI, Address::Memory0),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // 'BAD@
                (TestOp::Bits(RA, 0xff, 0x4a), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Load(RSI, Address::Bad),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // -ADDRESS@
                (TestOp::Bits(RA, 0xff, 0x4b), vec![
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Load(RSI, Address::NotAddress),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // BRANCH
                (TestOp::Bits(RA, 0xff, 0x4c), vec![], State::Branch),

                // BRANCHI
                (TestOp::Bits(RA, 0xff, 0x4d), vec![], State::Branchi),

                // ?BRANCH
                (TestOp::Bits(RA, 0xff, 0x4e), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                ], State::Qbranch),

                // ?BRANCHI
                (TestOp::Bits(RA, 0xff, 0x4f), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                ], State::Qbranchi),

                // EXECUTE
                (TestOp::Bits(RA, 0xff, 0x50), vec![
                    // Push EP onto the return stack.
                    Load(RD, B_RP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RD, RD, RSI),
                    Store(RD, B_RP),
                    Load(RA, B_EP),
                    Store(RA, Memory(RD)),
                    // Put a-addr1 into EP.
                    Load(RD, B_SP),
                    Load(RA, Memory(RD)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RD, RD, RSI),
                    Store(RD, B_SP),
                    Store(RA, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),

                // @EXECUTE
                (TestOp::Bits(RA, 0xff, 0x51), vec![
                    // Push EP onto the return stack.
                    Load(RD, B_RP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RD, RD, RSI),
                    Store(RD, B_RP),
                    Load(RA, B_EP),
                    Store(RA, Memory(RD)),
                    // Put the contents of a-addr1 into EP.
                    Load(RD, B_SP),
                    Load(RA, Memory(RD)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RD, RD, RSI),
                    Store(RD, B_SP),
                    Load(RA, Memory(RA)),
                    Store(RA, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),

                // CALL
                (TestOp::Bits(RA, 0xff, 0x52), vec![
                    // Push EP+4 onto the return stack.
                    Load(RD, B_RP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RD, RD, RSI),
                    Store(RD, B_RP),
                    Load(RA, B_EP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, Memory(RD)),
                ], State::Branch),

                // CALLI
                (TestOp::Bits(RA, 0xff, 0x53), vec![
                    // Push EP onto the return stack.
                    Load(RD, B_RP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RD, RD, RSI),
                    Store(RD, B_RP),
                    Load(RA, B_EP),
                    Store(RA, Memory(RD)),
                ], State::Branchi),

                // EXIT
                (TestOp::Bits(RA, 0xff, 0x54), vec![
                    // Put a-addr into EP.
                    Load(RD, B_RP),
                    Load(RA, Memory(RD)),
                    Store(RA, B_EP), // FIXME: Add check that EP is valid.
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RD, RD, RSI),
                    Store(RD, B_RP),
                ], State::Next),

                // (DO)
                (TestOp::Bits(RA, 0xff, 0x55), vec![
                    // Pop two items from SP.
                    Load(RA, B_SP),
                    Load(RSI, Memory(RA)),
                    Constant(RD, cell_bytes(1)),
                    Binary(Add, RA, RA, RD),
                    Load(RB, Memory(RA)),
                    Binary(Add, RA, RA, RD),
                    Store(RA, B_SP),
                    // Push two items to RP.
                    Load(RA, B_RP),
                    Constant(RD, cell_bytes(1)),
                    Binary(Sub, RA, RA, RD),
                    Store(RB, Memory(RA)),
                    Binary(Sub, RA, RA, RD),
                    Store(RSI, Memory(RA)),
                    Store(RA, B_RP),
                ], State::Root),

                // (LOOP)
                (TestOp::Bits(RA, 0xff, 0x56), vec![
                    // Load the index and limit from RP.
                    Load(RA, B_RP),
                    Load(RB, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RSI, RA, RSI),
                    Load(RSI, Memory(RSI)),
                    // Update the index.
                    Constant(RD, 1),
                    Binary(Add, RB, RB, RD),
                    Store(RB, Memory(RA)),
                    Binary(Sub, RB, RB, RSI),
                ], State::Loop),

                // (LOOP)I
                (TestOp::Bits(RA, 0xff, 0x57), vec![
                    // Load the index and limit from RP.
                    Load(RA, B_RP),
                    Load(RB, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RSI, RA, RSI),
                    Load(RSI, Memory(RSI)),
                    // Update the index.
                    Constant(RD, 1),
                    Binary(Add, RB, RB, RD),
                    Store(RB, Memory(RA)),
                    Binary(Sub, RB, RB, RSI),
                ], State::Loopi),

                // (+LOOP)
                (TestOp::Bits(RA, 0xff, 0x58), vec![
                    // Pop the step from SP.
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                    // Load the index and limit from RP.
                    Load(RA, B_RP),
                    Load(RB, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RSI, RA, RSI),
                    Load(RSI, Memory(RSI)),
                    // Update the index.
                    Binary(Add, RBP, RB, RD),
                    Store(RBP, Memory(RA)),
                    // Compute the differences between old and new indexes and limit.
                    Binary(Sub, RB, RB, RSI),
                    Binary(Sub, RBP, RBP, RSI),
                ], State::Ploop),

                // (+LOOP)I
                (TestOp::Bits(RA, 0xff, 0x59), vec![
                    // Pop the step from SP.
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_SP),
                    // Load the index and limit from RP.
                    Load(RA, B_RP),
                    Load(RB, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RSI, RA, RSI),
                    Load(RSI, Memory(RSI)),
                    // Update the index.
                    Binary(Add, RBP, RB, RD),
                    Store(RBP, Memory(RA)),
                    // Compute the differences between old and new indexes and limit.
                    Binary(Sub, RB, RB, RSI),
                    Binary(Sub, RBP, RBP, RSI),
                ], State::Ploopi),

                // UNLOOP
                (TestOp::Bits(RA, 0xff, 0x5a), vec![
                    // Discard two items from RP.
                    Load(RA, B_RP),
                    Constant(RD, cell_bytes(2)),
                    Binary(Add, RA, RA, RD),
                    Store(RA, B_RP),
                ], State::Root),

                // J
                (TestOp::Bits(RA, 0xff, 0x5b), vec![
                    // Push the third item of RP to SP.
                    Load(RA, B_RP),
                    Constant(RD, cell_bytes(2)),
                    Binary(Add, RA, RA, RD),
                    Load(RSI, Memory(RA)),
                    Load(RA, B_SP),
                    Constant(RD, cell_bytes(1)),
                    Binary(Sub, RA, RA, RD),
                    Store(RA, B_SP),
                    Store(RSI, Memory(RA)),
                ], State::Root),

                // (LITERAL)
                (TestOp::Bits(RA, 0xff, 0x5c), vec![
                    // Load RD from cell pointed to by EP, and add 4 to EP.
                    Load(RA, B_EP),
                    Load(RD, Memory(RA)),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Add, RA, RA, RSI),
                    Store(RA, B_EP), // FIXME: Add check that EP is valid.
                    // Push RD to the stack.
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Store(RA, B_SP),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // (LITERAL)I
                (TestOp::Bits(RA, 0xff, 0x5d), vec![
                    // Push A to the stack.
                    Load(RA, B_SP),
                    Constant(RSI, cell_bytes(1)),
                    Binary(Sub, RA, RA, RSI),
                    Store(RA, B_SP),
                    Load(RD, B_A),
                    Store(RD, Memory(RA)),
                ], State::Next),

                // THROW
                (TestOp::Bits(RA, 0xff, 0x5e), vec![
                    // Set 'BAD to EP
                    Load(RA, B_EP),
                    Store(RA, Address::Bad),
                    // Load EP from 'THROW
                    Load(RA, Address::Throw),
                    Load(RA, Memory(RA)),
                    Store(RA, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),
            ]},
        }
    }

    fn initial_states(&self) -> Vec<Self::State> {
        vec![State::Root]
    }
}
