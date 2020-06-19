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
    Abs,
    Max,
    Min,
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

    fn get_code(state: Self::State) -> Vec<(code::TestOp, Vec<Action>, Self::State)> {
        use super::x86_64::Register::{RA, RD, RC, RB, RBP};
        use Address::{EP as B_EP, A as B_A, SP as B_SP, RP as B_RP, Memory};
        match state {
            State::Root => {vec![
                (TestOp::Always, vec![
                    Load(RA, B_A),
                    Constant(RC, 8),
                    Binary(Asr, RD, RA, RC),
                    Store(RD, B_A),
                ], State::Dispatch),
            ]},
            State::Next => {vec![
                (TestOp::Always, vec![
                    Load(RA, B_EP), // FIXME: Add check that EP is valid.
                    Load(RD, Memory(RA)),
                    Store(RD, B_A),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
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
                            Constant(RC, cell_bytes(u + 1)),
                            Binary(Add, RD, RA, RC),
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
                        Constant(RC, cell_bytes(u)),
                        Binary(Add, RBP, RA, RC),
                        Load(RB, Memory(RBP)),
                    ];
                    for v in 0..u {
                        rollu.extend(vec![
                            Constant(RC, cell_bytes(v)),
                            Binary(Add, RC, RA, RC),
                            Load(RD, Memory(RC)),
                            Store(RB, Memory(RC)),
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
                     Constant(RC, cell_bytes(1)),
                     Binary(Sub, RA, RA, RC),
                     Store(RD, Memory(RA)),
                     Store(RA, B_SP),
                ], State::Root),
            ]},
            State::Abs => {vec![
                (TestOp::Lt(RD, 0), vec![
                    Unary(Negate, RD, RD),
                    Store(RD, Memory(RA)),
                ], State::Root),
                (TestOp::Ge(RD, 0), vec![], State::Root),
            ]},
            State::Max => {vec![
                (TestOp::Eq(RB, 0), vec![], State::Root),
                (TestOp::Ne(RB, 0), vec![
                    Store(RD, Memory(RA)),
                ], State::Root),
            ]},
            State::Min => {vec![
                (TestOp::Eq(RB, 0), vec![], State::Root),
                (TestOp::Ne(RB, 0), vec![
                    Store(RD, Memory(RA)),
                ], State::Root),
            ]},
            State::Lshift => {vec![
                (TestOp::Ult(RC, CELL_BITS), vec![
                    Binary(Lsl, RD, RD, RC),
                    Store(RD, Memory(RA)),
                ], State::Root),
                (TestOp::Uge(RC, CELL_BITS), vec![
                    Constant(RD, 0),
                    Store(RD, Memory(RA)),
                ], State::Root),
            ]},
            State::Rshift => {vec![
                (TestOp::Ult(RC, CELL_BITS), vec![
                    Binary(Lsr, RD, RD, RC),
                    Store(RD, Memory(RA)),
                ], State::Root),
                (TestOp::Uge(RC, CELL_BITS), vec![
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
                    Constant(RC, cell_bytes(1)),
                    Binary(Mul, RD, RD, RC),
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
                    Constant(RC, cell_bytes(2)),
                    Binary(Add, RA, RA, RC),
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
                    Constant(RC, cell_bytes(2)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_RP),
                ], State::Root),
                (TestOp::Ne(RB, 0), vec![], State::Branchi),
            ]},
            State::Ploopp => {vec![
                (TestOp::Lt(RBP, 0), vec![
                    // Discard the loop index and limit.
                    Load(RA, B_RP),
                    Constant(RC, cell_bytes(2)),
                    Binary(Add, RA, RA, RC),
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
                    Constant(RC, cell_bytes(2)),
                    Binary(Add, RA, RA, RC),
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
                    Constant(RC, cell_bytes(2)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_RP),
                ], State::Root),
                (TestOp::Ge(RBP, 0), vec![], State::Branchi),
            ]},
            State::Ploopim => {vec![
                (TestOp::Lt(RBP, 0), vec![
                    // Discard the loop index and limit.
                    Load(RA, B_RP),
                    Constant(RC, cell_bytes(2)),
                    Binary(Add, RA, RA, RC),
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
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // DROP
                (TestOp::Bits(RA, 0xff, 0x02), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                ], State::Root),

                // SWAP
                (TestOp::Bits(RA, 0xff, 0x03), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RD, RA, RC),
                    Load(RC, Memory(RA)),
                    Load(RB, Memory(RD)),
                    Store(RC, Memory(RD)),
                    Store(RB, Memory(RA)),
                ], State::Root),

                // OVER
                (TestOp::Bits(RA, 0xff, 0x04), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RD, RA, RC),
                    Load(RB, Memory(RD)),
                    Binary(Sub, RA, RA, RC),
                    Store(RB, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // ROT
                (TestOp::Bits(RA, 0xff, 0x05), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RBP, RA, RC),
                    Load(RB, Memory(RBP)),
                    Store(RD, Memory(RBP)),
                    Constant(RC, cell_bytes(2)),
                    Binary(Add, RBP, RA, RC),
                    Load(RD, Memory(RBP)),
                    Store(RB, Memory(RBP)),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // -ROT
                (TestOp::Bits(RA, 0xff, 0x06), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(2)),
                    Binary(Add, RBP, RA, RC),
                    Load(RB, Memory(RBP)),
                    Store(RD, Memory(RBP)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RBP, RA, RC),
                    Load(RD, Memory(RBP)),
                    Store(RB, Memory(RBP)),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // TUCK
                (TestOp::Bits(RA, 0xff, 0x07), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RBP, RA, RC),
                    Load(RB, Memory(RBP)),
                    Store(RD, Memory(RBP)),
                    Store(RB, Memory(RA)),
                    Binary(Sub, RA, RA, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // NIP
                (TestOp::Bits(RA, 0xff, 0x08), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
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
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
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
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                    Load(RA, B_RP),
                    Binary(Sub, RA, RA, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_RP),
                ], State::Root),

                // R>
                (TestOp::Bits(RA, 0xff, 0x0d), vec![
                    Load(RA, B_RP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_RP),
                    Load(RA, B_SP),
                    Binary(Sub, RA, RA, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // R@
                (TestOp::Bits(RA, 0xff, 0x0e), vec![
                    Load(RA, B_RP),
                    Load(RD, Memory(RA)),
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // <
                (TestOp::Bits(RA, 0xff, 0x0f), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(Lt, RD, RC, RD),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // >
                (TestOp::Bits(RA, 0xff, 0x10), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(Lt, RD, RD, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // =
                (TestOp::Bits(RA, 0xff, 0x11), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(Eq, RD, RD, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // <>
                (TestOp::Bits(RA, 0xff, 0x12), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(Eq, RD, RD, RC),
                    Unary(Not, RD, RD),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // 0<
                (TestOp::Bits(RA, 0xff, 0x13), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, 0),
                    Binary(Lt, RD, RD, RC),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // 0>
                (TestOp::Bits(RA, 0xff, 0x14), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, 0),
                    Binary(Lt, RD, RC, RD),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // 0=
                (TestOp::Bits(RA, 0xff, 0x15), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, 0),
                    Binary(Eq, RD, RC, RD),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // 0<>
                (TestOp::Bits(RA, 0xff, 0x16), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, 0),
                    Binary(Eq, RD, RC, RD),
                    Unary(Not, RD, RD),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // U<
                (TestOp::Bits(RA, 0xff, 0x17), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(Ult, RD, RC, RD),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // U>
                (TestOp::Bits(RA, 0xff, 0x18), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(Ult, RD, RD, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // 0
                (TestOp::Bits(RA, 0xff, 0x19), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Constant(RC, 0),
                    Store(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // 1
                (TestOp::Bits(RA, 0xff, 0x1a), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Constant(RC, 1),
                    Store(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // -1
                (TestOp::Bits(RA, 0xff, 0x1b), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Constant(RC, (-Wrapping(1u32)).0),
                    Store(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // CELL
                (TestOp::Bits(RA, 0xff, 0x1c), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Constant(RC, cell_bytes(1)),
                    Store(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // -CELL
                (TestOp::Bits(RA, 0xff, 0x1d), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Constant(RC, (-Wrapping(cell_bytes(1))).0),
                    Store(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // +
                (TestOp::Bits(RA, 0xff, 0x1e), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(Add, RD, RD, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // -
                (TestOp::Bits(RA, 0xff, 0x1f), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(Sub, RD, RD, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // >-<
                (TestOp::Bits(RA, 0xff, 0x20), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(Sub, RD, RC, RD),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // 1+
                (TestOp::Bits(RA, 0xff, 0x21), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, 1),
                    Binary(Add, RD, RD, RC),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // 1-
                (TestOp::Bits(RA, 0xff, 0x22), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, 1),
                    Binary(Sub, RD, RD, RC),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // CELL+
                (TestOp::Bits(RA, 0xff, 0x23), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RD, RD, RC),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // CELL-
                (TestOp::Bits(RA, 0xff, 0x24), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RD, RD, RC),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // *
                (TestOp::Bits(RA, 0xff, 0x25), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(Mul, RD, RD, RC),
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
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RC, RB, RC),
                    Load(RA, Memory(RC)),
                    Division(UnsignedDivMod, RA, RD, RA, RD),
                    Store(RD, Memory(RC)),
                    Store(RA, Memory(RB)),
                ], State::Root),

                // S/REM
                (TestOp::Bits(RA, 0xff, 0x2a), vec![
                    Load(RB, B_SP),
                    Load(RD, Memory(RB)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RC, RB, RC),
                    Load(RA, Memory(RC)),
                    Division(SignedDivMod, RA, RD, RA, RD),
                    Store(RD, Memory(RC)),
                    Store(RA, Memory(RB)),
                ], State::Root),

                // 2/
                (TestOp::Bits(RA, 0xff, 0x2b), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, 1),
                    Binary(Asr, RD, RD, RC),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // CELLS
                (TestOp::Bits(RA, 0xff, 0x2c), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Mul, RD, RD, RC),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // ABS
                (TestOp::Bits(RA, 0xff, 0x2d), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                ], State::Abs),

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
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                    Load(RC, Memory(RA)),
                    Binary(Lt, RB, RC, RD),
                ], State::Max),

                // MIN
                (TestOp::Bits(RA, 0xff, 0x30), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                    Load(RC, Memory(RA)),
                    Binary(Lt, RB, RD, RC),
                ], State::Min),

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
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(And, RD, RD, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // OR
                (TestOp::Bits(RA, 0xff, 0x33), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(Or, RD, RD, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // XOR
                (TestOp::Bits(RA, 0xff, 0x34), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Binary(Xor, RD, RD, RC),
                    Store(RD, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // LSHIFT
                (TestOp::Bits(RA, 0xff, 0x35), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Lshift),

                // RSHIFT
                (TestOp::Bits(RA, 0xff, 0x36), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Load(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Rshift),

                // 1LSHIFT
                (TestOp::Bits(RA, 0xff, 0x37), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, 1),
                    Binary(Lsl, RD, RD, RC),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // 1RSHIFT
                (TestOp::Bits(RA, 0xff, 0x38), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, 1),
                    Binary(Lsr, RD, RD, RC),
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
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RC, RA, RC),
                    Load(RB, Memory(RC)),
                    Store(RB, Memory(RD)),
                    Constant(RC, cell_bytes(2)),
                    Binary(Add, RA, RA, RC),
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
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RC, RA, RC),
                    Load(RB, Memory(RC)),
                    StoreNarrow(Width::One, RB, Memory(RD)),
                    Constant(RC, cell_bytes(2)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                ], State::Root),

                // +!
                (TestOp::Bits(RA, 0xff, 0x3d), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RC, RA, RC),
                    Load(RB, Memory(RC)),
                    Load(RBP, Memory(RD)),
                    Binary(Add, RB, RBP, RB),
                    Store(RB, Memory(RD)),
                    Constant(RC, cell_bytes(2)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                ], State::Root),

                // SP@
                (TestOp::Bits(RA, 0xff, 0x3e), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RC, RA, RC),
                    Store(RA, Memory(RC)),
                    Store(RC, B_SP),
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
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Load(RC, B_RP),
                    Store(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // RP!
                (TestOp::Bits(RA, 0xff, 0x41), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Store(RD, B_RP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                ], State::Root),

                // EP@
                (TestOp::Bits(RA, 0xff, 0x42), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Load(RC, B_EP),
                    Store(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // S0@
                (TestOp::Bits(RA, 0xff, 0x43), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Load(RC, Address::S0),
                    Store(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // S0!
                (TestOp::Bits(RA, 0xff, 0x44), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Store(RD, Address::S0),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                ], State::Root),

                // R0@
                (TestOp::Bits(RA, 0xff, 0x45), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Load(RC, Address::R0),
                    Store(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // R0!
                (TestOp::Bits(RA, 0xff, 0x46), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Store(RD, Address::R0),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                ], State::Root),

                // 'THROW@
                (TestOp::Bits(RA, 0xff, 0x47), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Load(RC, Address::Throw),
                    Store(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // 'THROW!
                (TestOp::Bits(RA, 0xff, 0x48), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Store(RD, Address::Throw),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                ], State::Root),

                // MEMORY@
                (TestOp::Bits(RA, 0xff, 0x49), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Load(RC, Address::Memory0),
                    Store(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // 'BAD@
                (TestOp::Bits(RA, 0xff, 0x4a), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Load(RC, Address::Bad),
                    Store(RC, Memory(RA)),
                    Store(RA, B_SP),
                ], State::Root),

                // -ADDRESS@
                (TestOp::Bits(RA, 0xff, 0x4b), vec![
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Load(RC, Address::NotAddress),
                    Store(RC, Memory(RA)),
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
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                ], State::Qbranch),

                // ?BRANCHI
                (TestOp::Bits(RA, 0xff, 0x4f), vec![
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                ], State::Qbranchi),

                // EXECUTE
                (TestOp::Bits(RA, 0xff, 0x50), vec![
                    // Push EP onto the return stack.
                    Load(RD, B_RP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RD, RD, RC),
                    Store(RD, B_RP),
                    Load(RA, B_EP),
                    Store(RA, Memory(RD)),
                    // Put a-addr1 into EP.
                    Load(RD, B_SP),
                    Load(RA, Memory(RD)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RD, RD, RC),
                    Store(RD, B_SP),
                    Store(RA, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),

                // @EXECUTE
                (TestOp::Bits(RA, 0xff, 0x51), vec![
                    // Push EP onto the return stack.
                    Load(RD, B_RP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RD, RD, RC),
                    Store(RD, B_RP),
                    Load(RA, B_EP),
                    Store(RA, Memory(RD)),
                    // Put the contents of a-addr1 into EP.
                    Load(RD, B_SP),
                    Load(RA, Memory(RD)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RD, RD, RC),
                    Store(RD, B_SP),
                    Load(RA, Memory(RA)),
                    Store(RA, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),

                // CALL
                (TestOp::Bits(RA, 0xff, 0x52), vec![
                    // Push EP+4 onto the return stack.
                    Load(RD, B_RP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RD, RD, RC),
                    Store(RD, B_RP),
                    Load(RA, B_EP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, Memory(RD)),
                ], State::Branch),

                // CALLI
                (TestOp::Bits(RA, 0xff, 0x53), vec![
                    // Push EP onto the return stack.
                    Load(RD, B_RP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RD, RD, RC),
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
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RD, RD, RC),
                    Store(RD, B_RP),
                ], State::Next),

                // (DO)
                (TestOp::Bits(RA, 0xff, 0x55), vec![
                    // Pop two items from SP.
                    Load(RA, B_SP),
                    Load(RC, Memory(RA)),
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
                    Store(RC, Memory(RA)),
                    Store(RA, B_RP),
                ], State::Root),

                // (LOOP)
                (TestOp::Bits(RA, 0xff, 0x56), vec![
                    // Load the index and limit from RP.
                    Load(RA, B_RP),
                    Load(RB, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RC, RA, RC),
                    Load(RC, Memory(RC)),
                    // Update the index.
                    Constant(RD, 1),
                    Binary(Add, RB, RB, RD),
                    Store(RB, Memory(RA)),
                    Binary(Sub, RB, RB, RC),
                ], State::Loop),

                // (LOOP)I
                (TestOp::Bits(RA, 0xff, 0x57), vec![
                    // Load the index and limit from RP.
                    Load(RA, B_RP),
                    Load(RB, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RC, RA, RC),
                    Load(RC, Memory(RC)),
                    // Update the index.
                    Constant(RD, 1),
                    Binary(Add, RB, RB, RD),
                    Store(RB, Memory(RA)),
                    Binary(Sub, RB, RB, RC),
                ], State::Loopi),

                // (+LOOP)
                (TestOp::Bits(RA, 0xff, 0x58), vec![
                    // Pop the step from SP.
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                    // Load the index and limit from RP.
                    Load(RA, B_RP),
                    Load(RB, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RC, RA, RC),
                    Load(RC, Memory(RC)),
                    // Update the index.
                    Binary(Add, RBP, RB, RD),
                    Store(RBP, Memory(RA)),
                    // Compute the differences between old and new indexes and limit.
                    Binary(Sub, RB, RB, RC),
                    Binary(Sub, RBP, RBP, RC),
                ], State::Ploop),

                // (+LOOP)I
                (TestOp::Bits(RA, 0xff, 0x59), vec![
                    // Pop the step from SP.
                    Load(RA, B_SP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_SP),
                    // Load the index and limit from RP.
                    Load(RA, B_RP),
                    Load(RB, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RC, RA, RC),
                    Load(RC, Memory(RC)),
                    // Update the index.
                    Binary(Add, RBP, RB, RD),
                    Store(RBP, Memory(RA)),
                    // Compute the differences between old and new indexes and limit.
                    Binary(Sub, RB, RB, RC),
                    Binary(Sub, RBP, RBP, RC),
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
                    Load(RC, Memory(RA)),
                    Load(RA, B_SP),
                    Constant(RD, cell_bytes(1)),
                    Binary(Sub, RA, RA, RD),
                    Store(RA, B_SP),
                    Store(RC, Memory(RA)),
                ], State::Root),

                // (LITERAL)
                (TestOp::Bits(RA, 0xff, 0x5c), vec![
                    // Load RD from cell pointed to by EP, and add 4 to EP.
                    Load(RA, B_EP),
                    Load(RD, Memory(RA)),
                    Constant(RC, cell_bytes(1)),
                    Binary(Add, RA, RA, RC),
                    Store(RA, B_EP), // FIXME: Add check that EP is valid.
                    // Push RD to the stack.
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
                    Store(RA, B_SP),
                    Store(RD, Memory(RA)),
                ], State::Root),

                // (LITERAL)I
                (TestOp::Bits(RA, 0xff, 0x5d), vec![
                    // Push A to the stack.
                    Load(RA, B_SP),
                    Constant(RC, cell_bytes(1)),
                    Binary(Sub, RA, RA, RC),
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
}
