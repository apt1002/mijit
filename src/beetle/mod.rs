use std::num::{Wrapping};

use super::code::{
    self, TestOp, Precision, MemoryLocation, UnaryOp, BinaryOp, DivisionOp,
};
use code::Action::*;
use MemoryLocation::*;
use UnaryOp::*;
use BinaryOp::*;
use DivisionOp::*;
use Precision::*;

use super::x86_64::Register::{RA, RD, RB, RBP, RSI};

pub type Action = code::Action<Memory, Global>;

/** Beetle has only one memory. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Memory {M}

impl code::Alias for Memory {}

/** Beetle's registers. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Global {
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
}

/** Computes the number of bytes in `n` words. */
pub const fn cell_bytes(n: i64) -> i64 { Wrapping(4 * n).0 }

/** The number of bits in a word. */
pub const CELL_BITS: i64 = cell_bytes(8);

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

impl code::Machine for Machine {
    type State = State;
    type Memory = Memory;
    type Global = Global;

    fn get_code(&self, state: Self::State) -> Vec<((TestOp, Precision), Vec<Action>, Self::State)> {
        // TODO: Every memory address has to be bounds-checked and added to `M0`.
        use Global::{EP as B_EP, A as B_A, SP as B_SP, RP as B_RP};
        match state {
            State::Root => {vec![
                ((TestOp::Always, P32), vec![
                    LoadGlobal(RA, B_A),
                    Constant(P32, RSI, 8),
                    Binary(Asr, P32, RD, RA, RSI),
                    StoreGlobal(RD, B_A),
                ], State::Dispatch),
            ]},
            State::Next => {vec![
                ((TestOp::Always, P32), vec![
                    LoadGlobal(RA, B_EP), // FIXME: Add check that EP is valid.
                    Load(P32, RD, Four(RA, Memory::M)),
                    StoreGlobal(RD, B_A),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_EP),
                ], State::Root),
            ]},
            State::Pick => {
                let mut pick = Vec::new();
                for u in 0..4 {
                    pick.push((
                        (TestOp::Eq(RD, u), P32),
                        vec![
                            LoadGlobal(RA, B_SP),
                            Constant(P32, RSI, cell_bytes(u as i64 + 1)),
                            Binary(Add, P32, RD, RA, RSI),
                            Load(P32, RD, Four(RD, Memory::M)),
                            Store(RD, Four(RA, Memory::M)),
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
                        Constant(P32, RSI, cell_bytes(u)),
                        Binary(Add, P32, RBP, RA, RSI),
                        Load(P32, RB, Four(RBP, Memory::M)),
                    ];
                    for v in 0..u {
                        rollu.extend(vec![
                            Constant(P32, RSI, cell_bytes(v)),
                            Binary(Add, P32, RSI, RA, RSI),
                            Load(P32, RD, Four(RSI, Memory::M)),
                            Store(RB, Four(RSI, Memory::M)),
                            Move(P32, RB, RD),
                        ]);
                    }
                    rollu.extend(vec![
                        Store(RB, Four(RBP, Memory::M)),
                    ]);
                    roll.push((
                        (TestOp::Eq(RD, u as i32), P32),
                        rollu,
                        State::Root,
                    ));
                }
                roll
            },
            State::Qdup => {vec![
                ((TestOp::Eq(RD, 0), P32), vec![], State::Root),
                ((TestOp::Ne(RD, 0), P32), vec![
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),
            ]},
            State::Lshift => {vec![
                ((TestOp::Ult(RSI, CELL_BITS as i32), P32), vec![
                    Binary(Lsl, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),
                ((TestOp::Uge(RSI, CELL_BITS as i32), P32), vec![
                    Constant(P32, RD, 0),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),
            ]},
            State::Rshift => {vec![
                ((TestOp::Ult(RSI, CELL_BITS as i32), P32), vec![
                    Binary(Lsr, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),
                ((TestOp::Uge(RSI, CELL_BITS as i32), P32), vec![
                    Constant(P32, RD, 0),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),
            ]},
            State::Branch => {vec![
                ((TestOp::Always, P32), vec![
                    // Load EP from the cell it points to.
                    LoadGlobal(RA, B_EP),
                    Load(P32, RA, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),
            ]},
            State::Branchi => {vec![
                ((TestOp::Always, P32), vec![
                    LoadGlobal(RA, B_EP),
                    LoadGlobal(RD, B_A),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Mul, P32, RD, RD, RSI),
                    Binary(Add, P32, RA, RA, RD),
                    StoreGlobal(RA, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),
            ]},
            State::Qbranch => {vec![
                ((TestOp::Eq(RD, 0), P32), vec![], State::Branch),
                ((TestOp::Ne(RD, 0), P32), vec![
                    LoadGlobal(RA, B_EP),
                    Constant(P32, RD, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RD),
                    StoreGlobal(RA, B_EP),
                ], State::Root),
            ]},
            State::Qbranchi => {vec![
                ((TestOp::Eq(RD, 0), P32), vec![], State::Branchi),
                ((TestOp::Ne(RD, 0), P32), vec![], State::Root),
            ]},
            State::Loop => {vec![
                ((TestOp::Eq(RB, 0), P32), vec![
                    // Discard the loop index and limit.
                    LoadGlobal(RA, B_RP),
                    Constant(P32, RSI, cell_bytes(2)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_RP),
                    // Add 4 to EP.
                    LoadGlobal(RA, B_EP), // FIXME: Add check that EP is valid.
                    Constant(P32, RD, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RD),
                    StoreGlobal(RA, B_EP),
                ], State::Root),
                ((TestOp::Ne(RB, 0), P32), vec![], State::Branch),
            ]},
            State::Loopi => {vec![
                ((TestOp::Eq(RB, 0), P32), vec![
                    // Discard the loop index and limit.
                    LoadGlobal(RA, B_RP),
                    Constant(P32, RSI, cell_bytes(2)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_RP),
                ], State::Root),
                ((TestOp::Ne(RB, 0), P32), vec![], State::Branchi),
            ]},
            State::Ploopp => {vec![
                ((TestOp::Lt(RBP, 0), P32), vec![
                    // Discard the loop index and limit.
                    LoadGlobal(RA, B_RP),
                    Constant(P32, RSI, cell_bytes(2)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_RP),
                    // Add 4 to EP.
                    LoadGlobal(RA, B_EP), // FIXME: Add check that EP is valid.
                    Constant(P32, RD, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RD),
                    StoreGlobal(RA, B_EP),
                ], State::Root),
                ((TestOp::Ge(RBP, 0), P32), vec![], State::Branch),
            ]},
            State::Ploopm => {vec![
                ((TestOp::Lt(RBP, 0), P32), vec![
                    // Discard the loop index and limit.
                    LoadGlobal(RA, B_RP),
                    Constant(P32, RSI, cell_bytes(2)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_RP),
                    // Add 4 to EP.
                    LoadGlobal(RA, B_EP), // FIXME: Add check that EP is valid.
                    Constant(P32, RD, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RD),
                    StoreGlobal(RA, B_EP),
                ], State::Root),
                ((TestOp::Ge(RBP, 0), P32), vec![], State::Branch),
            ]},
            State::Ploop => {vec![
                ((TestOp::Ge(RD, 0), P32), vec![
                    Unary(Not, P32, RBP, RBP),
                    Binary(And, P32, RBP, RBP, RB),
                ], State::Ploopp),
                ((TestOp::Lt(RD, 0), P32), vec![
                    Unary(Not, P32, RB, RB),
                    Binary(And, P32, RBP, RBP, RB),
                ], State::Ploopm),
            ]},
            State::Ploopip => {vec![
                ((TestOp::Lt(RBP, 0), P32), vec![
                    // Discard the loop index and limit.
                    LoadGlobal(RA, B_RP),
                    Constant(P32, RSI, cell_bytes(2)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_RP),
                ], State::Root),
                ((TestOp::Ge(RBP, 0), P32), vec![], State::Branchi),
            ]},
            State::Ploopim => {vec![
                ((TestOp::Lt(RBP, 0), P32), vec![
                    // Discard the loop index and limit.
                    LoadGlobal(RA, B_RP),
                    Constant(P32, RSI, cell_bytes(2)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_RP),
                ], State::Root),
                ((TestOp::Ge(RBP, 0), P32), vec![], State::Branchi),
            ]},
            State::Ploopi => {vec![
                ((TestOp::Ge(RD, 0), P32), vec![
                    Unary(Not, P32, RBP, RBP),
                    Binary(And, P32, RBP, RBP, RB),
                ], State::Ploopip),
                ((TestOp::Lt(RD, 0), P32), vec![
                    Unary(Not, P32, RB, RB),
                    Binary(And, P32, RBP, RBP, RB),
                ], State::Ploopim),
            ]},
            State::Dispatch => {vec![
                // NEXT
                ((TestOp::Bits(RA, 0xff, 0x00), P32), vec![], State::Next),

                // DUP
                ((TestOp::Bits(RA, 0xff, 0x01), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // DROP
                ((TestOp::Bits(RA, 0xff, 0x02), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // SWAP
                ((TestOp::Bits(RA, 0xff, 0x03), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RD, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Load(P32, RB, Four(RD, Memory::M)),
                    Store(RSI, Four(RD, Memory::M)),
                    Store(RB, Four(RA, Memory::M)),
                ], State::Root),

                // OVER
                ((TestOp::Bits(RA, 0xff, 0x04), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RD, RA, RSI),
                    Load(P32, RB, Four(RD, Memory::M)),
                    Binary(Sub, P32, RA, RA, RSI),
                    Store(RB, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // ROT
                ((TestOp::Bits(RA, 0xff, 0x05), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RBP, RA, RSI),
                    Load(P32, RB, Four(RBP, Memory::M)),
                    Store(RD, Four(RBP, Memory::M)),
                    Constant(P32, RSI, cell_bytes(2)),
                    Binary(Add, P32, RBP, RA, RSI),
                    Load(P32, RD, Four(RBP, Memory::M)),
                    Store(RB, Four(RBP, Memory::M)),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // -ROT
                ((TestOp::Bits(RA, 0xff, 0x06), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(2)),
                    Binary(Add, P32, RBP, RA, RSI),
                    Load(P32, RB, Four(RBP, Memory::M)),
                    Store(RD, Four(RBP, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RBP, RA, RSI),
                    Load(P32, RD, Four(RBP, Memory::M)),
                    Store(RB, Four(RBP, Memory::M)),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // TUCK
                ((TestOp::Bits(RA, 0xff, 0x07), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RBP, RA, RSI),
                    Load(P32, RB, Four(RBP, Memory::M)),
                    Store(RD, Four(RBP, Memory::M)),
                    Store(RB, Four(RA, Memory::M)),
                    Binary(Sub, P32, RA, RA, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // NIP
                ((TestOp::Bits(RA, 0xff, 0x08), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // PICK
                ((TestOp::Bits(RA, 0xff, 0x09), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                ], State::Pick),

                // ROLL
                ((TestOp::Bits(RA, 0xff, 0x0a), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                ], State::Roll),

                // ?DUP
                ((TestOp::Bits(RA, 0xff, 0x0b), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                ], State::Qdup),

                // >R
                ((TestOp::Bits(RA, 0xff, 0x0c), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                    LoadGlobal(RA, B_RP),
                    Binary(Sub, P32, RA, RA, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_RP),
                ], State::Root),

                // R>
                ((TestOp::Bits(RA, 0xff, 0x0d), P32), vec![
                    LoadGlobal(RA, B_RP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_RP),
                    LoadGlobal(RA, B_SP),
                    Binary(Sub, P32, RA, RA, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // R@
                ((TestOp::Bits(RA, 0xff, 0x0e), P32), vec![
                    LoadGlobal(RA, B_RP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // <
                ((TestOp::Bits(RA, 0xff, 0x0f), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Lt, P32, RD, RSI, RD),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // >
                ((TestOp::Bits(RA, 0xff, 0x10), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Lt, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // =
                ((TestOp::Bits(RA, 0xff, 0x11), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Eq, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // <>
                ((TestOp::Bits(RA, 0xff, 0x12), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Eq, P32, RD, RD, RSI),
                    Unary(Not, P32, RD, RD),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // 0<
                ((TestOp::Bits(RA, 0xff, 0x13), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, 0),
                    Binary(Lt, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // 0>
                ((TestOp::Bits(RA, 0xff, 0x14), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, 0),
                    Binary(Lt, P32, RD, RSI, RD),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // 0=
                ((TestOp::Bits(RA, 0xff, 0x15), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, 0),
                    Binary(Eq, P32, RD, RSI, RD),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // 0<>
                ((TestOp::Bits(RA, 0xff, 0x16), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, 0),
                    Binary(Eq, P32, RD, RSI, RD),
                    Unary(Not, P32, RD, RD),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // U<
                ((TestOp::Bits(RA, 0xff, 0x17), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Ult, P32, RD, RSI, RD),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // U>
                ((TestOp::Bits(RA, 0xff, 0x18), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Ult, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // 0
                ((TestOp::Bits(RA, 0xff, 0x19), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    Constant(P32, RSI, 0),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // 1
                ((TestOp::Bits(RA, 0xff, 0x1a), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    Constant(P32, RSI, 1),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // -1
                ((TestOp::Bits(RA, 0xff, 0x1b), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    Constant(P32, RSI, -1),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // CELL
                ((TestOp::Bits(RA, 0xff, 0x1c), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    Constant(P32, RSI, cell_bytes(1)),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // -CELL
                ((TestOp::Bits(RA, 0xff, 0x1d), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    Constant(P32, RSI, (-Wrapping(cell_bytes(1))).0),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // +
                ((TestOp::Bits(RA, 0xff, 0x1e), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Add, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // -
                ((TestOp::Bits(RA, 0xff, 0x1f), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Sub, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // >-<
                ((TestOp::Bits(RA, 0xff, 0x20), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Sub, P32, RD, RSI, RD),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // 1+
                ((TestOp::Bits(RA, 0xff, 0x21), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, 1),
                    Binary(Add, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // 1-
                ((TestOp::Bits(RA, 0xff, 0x22), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, 1),
                    Binary(Sub, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // CELL+
                ((TestOp::Bits(RA, 0xff, 0x23), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // CELL-
                ((TestOp::Bits(RA, 0xff, 0x24), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // *
                ((TestOp::Bits(RA, 0xff, 0x25), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Mul, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // /
                ((TestOp::Bits(RA, 0xff, 0x26), P32), vec![
                    // TODO
                ], State::Root),

                // MOD
                ((TestOp::Bits(RA, 0xff, 0x27), P32), vec![
                    // TODO
                ], State::Root),

                // /MOD
                ((TestOp::Bits(RA, 0xff, 0x28), P32), vec![
                    // TODO
                ], State::Root),

                // U/MOD
                ((TestOp::Bits(RA, 0xff, 0x29), P32), vec![
                    LoadGlobal(RB, B_SP),
                    Load(P32, RD, Four(RB, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RSI, RB, RSI),
                    Load(P32, RA, Four(RSI, Memory::M)),
                    Division(UnsignedDivMod, P32, RA, RD, RA, RD),
                    Store(RD, Four(RSI, Memory::M)),
                    Store(RA, Four(RB, Memory::M)),
                ], State::Root),

                // S/REM
                ((TestOp::Bits(RA, 0xff, 0x2a), P32), vec![
                    LoadGlobal(RB, B_SP),
                    Load(P32, RD, Four(RB, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RSI, RB, RSI),
                    Load(P32, RA, Four(RSI, Memory::M)),
                    Division(SignedDivMod, P32, RA, RD, RA, RD),
                    Store(RD, Four(RSI, Memory::M)),
                    Store(RA, Four(RB, Memory::M)),
                ], State::Root),

                // 2/
                ((TestOp::Bits(RA, 0xff, 0x2b), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, 1),
                    Binary(Asr, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // CELLS
                ((TestOp::Bits(RA, 0xff, 0x2c), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Mul, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // ABS
                ((TestOp::Bits(RA, 0xff, 0x2d), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Unary(Abs, P32, RD, RD),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // NEGATE
                ((TestOp::Bits(RA, 0xff, 0x2e), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Unary(Negate, P32, RD, RD),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // MAX
                ((TestOp::Bits(RA, 0xff, 0x2f), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Max, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // MIN
                ((TestOp::Bits(RA, 0xff, 0x30), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Min, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // INVERT
                ((TestOp::Bits(RA, 0xff, 0x31), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Unary(Not, P32, RD, RD),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // AND
                ((TestOp::Bits(RA, 0xff, 0x32), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(And, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // OR
                ((TestOp::Bits(RA, 0xff, 0x33), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Or, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // XOR
                ((TestOp::Bits(RA, 0xff, 0x34), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Binary(Xor, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // LSHIFT
                ((TestOp::Bits(RA, 0xff, 0x35), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Lshift),

                // RSHIFT
                ((TestOp::Bits(RA, 0xff, 0x36), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Rshift),

                // 1LSHIFT
                ((TestOp::Bits(RA, 0xff, 0x37), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, 1),
                    Binary(Lsl, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // 1RSHIFT
                ((TestOp::Bits(RA, 0xff, 0x38), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, 1),
                    Binary(Lsr, P32, RD, RD, RSI),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // @
                ((TestOp::Bits(RA, 0xff, 0x39), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Load(P32, RD, Four(RD, Memory::M)),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // !
                ((TestOp::Bits(RA, 0xff, 0x3a), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RSI, RA, RSI),
                    Load(P32, RB, Four(RSI, Memory::M)),
                    Store(RB, Four(RD, Memory::M)),
                    Constant(P32, RSI, cell_bytes(2)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // C@
                ((TestOp::Bits(RA, 0xff, 0x3b), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Load(P32, RD, One(RD, Memory::M)),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // C!
                ((TestOp::Bits(RA, 0xff, 0x3c), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RSI, RA, RSI),
                    Load(P32, RB, Four(RSI, Memory::M)),
                    Store(RB, One(RD, Memory::M)),
                    Constant(P32, RSI, cell_bytes(2)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // +!
                ((TestOp::Bits(RA, 0xff, 0x3d), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RSI, RA, RSI),
                    Load(P32, RB, Four(RSI, Memory::M)),
                    Load(P32, RBP, Four(RD, Memory::M)),
                    Binary(Add, P32, RB, RBP, RB),
                    Store(RB, Four(RD, Memory::M)),
                    Constant(P32, RSI, cell_bytes(2)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // SP@
                ((TestOp::Bits(RA, 0xff, 0x3e), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RSI, RA, RSI),
                    Store(RA, Four(RSI, Memory::M)),
                    StoreGlobal(RSI, B_SP),
                ], State::Root),

                // SP!
                ((TestOp::Bits(RA, 0xff, 0x3f), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RA, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // RP@
                ((TestOp::Bits(RA, 0xff, 0x40), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    LoadGlobal(RSI, B_RP),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // RP!
                ((TestOp::Bits(RA, 0xff, 0x41), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    StoreGlobal(RD, B_RP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // EP@
                ((TestOp::Bits(RA, 0xff, 0x42), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    LoadGlobal(RSI, B_EP),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // S0@
                ((TestOp::Bits(RA, 0xff, 0x43), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    LoadGlobal(RSI, Global::S0),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // S0!
                ((TestOp::Bits(RA, 0xff, 0x44), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    StoreGlobal(RD, Global::S0),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // R0@
                ((TestOp::Bits(RA, 0xff, 0x45), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    LoadGlobal(RSI, Global::R0),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // R0!
                ((TestOp::Bits(RA, 0xff, 0x46), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    StoreGlobal(RD, Global::R0),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // 'THROW@
                ((TestOp::Bits(RA, 0xff, 0x47), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    LoadGlobal(RSI, Global::Throw),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // 'THROW!
                ((TestOp::Bits(RA, 0xff, 0x48), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    StoreGlobal(RD, Global::Throw),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // MEMORY@
                ((TestOp::Bits(RA, 0xff, 0x49), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    LoadGlobal(RSI, Global::Memory0),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // 'BAD@
                ((TestOp::Bits(RA, 0xff, 0x4a), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    LoadGlobal(RSI, Global::Bad),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // -ADDRESS@
                ((TestOp::Bits(RA, 0xff, 0x4b), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    LoadGlobal(RSI, Global::NotAddress),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_SP),
                ], State::Root),

                // BRANCH
                ((TestOp::Bits(RA, 0xff, 0x4c), P32), vec![], State::Branch),

                // BRANCHI
                ((TestOp::Bits(RA, 0xff, 0x4d), P32), vec![], State::Branchi),

                // ?BRANCH
                ((TestOp::Bits(RA, 0xff, 0x4e), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                ], State::Qbranch),

                // ?BRANCHI
                ((TestOp::Bits(RA, 0xff, 0x4f), P32), vec![
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                ], State::Qbranchi),

                // EXECUTE
                ((TestOp::Bits(RA, 0xff, 0x50), P32), vec![
                    // Push EP onto the return stack.
                    LoadGlobal(RD, B_RP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RD, RD, RSI),
                    StoreGlobal(RD, B_RP),
                    LoadGlobal(RA, B_EP),
                    Store(RA, Four(RD, Memory::M)),
                    // Put a-addr1 into EP.
                    LoadGlobal(RD, B_SP),
                    Load(P32, RA, Four(RD, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RD, RD, RSI),
                    StoreGlobal(RD, B_SP),
                    StoreGlobal(RA, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),

                // @EXECUTE
                ((TestOp::Bits(RA, 0xff, 0x51), P32), vec![
                    // Push EP onto the return stack.
                    LoadGlobal(RD, B_RP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RD, RD, RSI),
                    StoreGlobal(RD, B_RP),
                    LoadGlobal(RA, B_EP),
                    Store(RA, Four(RD, Memory::M)),
                    // Put the contents of a-addr1 into EP.
                    LoadGlobal(RD, B_SP),
                    Load(P32, RA, Four(RD, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RD, RD, RSI),
                    StoreGlobal(RD, B_SP),
                    Load(P32, RA, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),

                // CALL
                ((TestOp::Bits(RA, 0xff, 0x52), P32), vec![
                    // Push EP+4 onto the return stack.
                    LoadGlobal(RD, B_RP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RD, RD, RSI),
                    StoreGlobal(RD, B_RP),
                    LoadGlobal(RA, B_EP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    Store(RA, Four(RD, Memory::M)),
                ], State::Branch),

                // CALLI
                ((TestOp::Bits(RA, 0xff, 0x53), P32), vec![
                    // Push EP onto the return stack.
                    LoadGlobal(RD, B_RP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RD, RD, RSI),
                    StoreGlobal(RD, B_RP),
                    LoadGlobal(RA, B_EP),
                    Store(RA, Four(RD, Memory::M)),
                ], State::Branchi),

                // EXIT
                ((TestOp::Bits(RA, 0xff, 0x54), P32), vec![
                    // Put a-addr into EP.
                    LoadGlobal(RD, B_RP),
                    Load(P32, RA, Four(RD, Memory::M)),
                    StoreGlobal(RA, B_EP), // FIXME: Add check that EP is valid.
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RD, RD, RSI),
                    StoreGlobal(RD, B_RP),
                ], State::Next),

                // (DO)
                ((TestOp::Bits(RA, 0xff, 0x55), P32), vec![
                    // Pop two items from SP.
                    LoadGlobal(RA, B_SP),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    Constant(P32, RD, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RD),
                    Load(P32, RB, Four(RA, Memory::M)),
                    Binary(Add, P32, RA, RA, RD),
                    StoreGlobal(RA, B_SP),
                    // Push two items to RP.
                    LoadGlobal(RA, B_RP),
                    Constant(P32, RD, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RD),
                    Store(RB, Four(RA, Memory::M)),
                    Binary(Sub, P32, RA, RA, RD),
                    Store(RSI, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_RP),
                ], State::Root),

                // (LOOP)
                ((TestOp::Bits(RA, 0xff, 0x56), P32), vec![
                    // Load the index and limit from RP.
                    LoadGlobal(RA, B_RP),
                    Load(P32, RB, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RSI, RA, RSI),
                    Load(P32, RSI, Four(RSI, Memory::M)),
                    // Update the index.
                    Constant(P32, RD, 1),
                    Binary(Add, P32, RB, RB, RD),
                    Store(RB, Four(RA, Memory::M)),
                    Binary(Sub, P32, RB, RB, RSI),
                ], State::Loop),

                // (LOOP)I
                ((TestOp::Bits(RA, 0xff, 0x57), P32), vec![
                    // Load the index and limit from RP.
                    LoadGlobal(RA, B_RP),
                    Load(P32, RB, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RSI, RA, RSI),
                    Load(P32, RSI, Four(RSI, Memory::M)),
                    // Update the index.
                    Constant(P32, RD, 1),
                    Binary(Add, P32, RB, RB, RD),
                    Store(RB, Four(RA, Memory::M)),
                    Binary(Sub, P32, RB, RB, RSI),
                ], State::Loopi),

                // (+LOOP)
                ((TestOp::Bits(RA, 0xff, 0x58), P32), vec![
                    // Pop the step from SP.
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                    // Load the index and limit from RP.
                    LoadGlobal(RA, B_RP),
                    Load(P32, RB, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RSI, RA, RSI),
                    Load(P32, RSI, Four(RSI, Memory::M)),
                    // Update the index.
                    Binary(Add, P32, RBP, RB, RD),
                    Store(RBP, Four(RA, Memory::M)),
                    // Compute the differences between old and new indexes and limit.
                    Binary(Sub, P32, RB, RB, RSI),
                    Binary(Sub, P32, RBP, RBP, RSI),
                ], State::Ploop),

                // (+LOOP)I
                ((TestOp::Bits(RA, 0xff, 0x59), P32), vec![
                    // Pop the step from SP.
                    LoadGlobal(RA, B_SP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                    // Load the index and limit from RP.
                    LoadGlobal(RA, B_RP),
                    Load(P32, RB, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RSI, RA, RSI),
                    Load(P32, RSI, Four(RSI, Memory::M)),
                    // Update the index.
                    Binary(Add, P32, RBP, RB, RD),
                    Store(RBP, Four(RA, Memory::M)),
                    // Compute the differences between old and new indexes and limit.
                    Binary(Sub, P32, RB, RB, RSI),
                    Binary(Sub, P32, RBP, RBP, RSI),
                ], State::Ploopi),

                // UNLOOP
                ((TestOp::Bits(RA, 0xff, 0x5a), P32), vec![
                    // Discard two items from RP.
                    LoadGlobal(RA, B_RP),
                    Constant(P32, RD, cell_bytes(2)),
                    Binary(Add, P32, RA, RA, RD),
                    StoreGlobal(RA, B_RP),
                ], State::Root),

                // J
                ((TestOp::Bits(RA, 0xff, 0x5b), P32), vec![
                    // Push the third item of RP to SP.
                    LoadGlobal(RA, B_RP),
                    Constant(P32, RD, cell_bytes(2)),
                    Binary(Add, P32, RA, RA, RD),
                    Load(P32, RSI, Four(RA, Memory::M)),
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RD, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RD),
                    StoreGlobal(RA, B_SP),
                    Store(RSI, Four(RA, Memory::M)),
                ], State::Root),

                // (LITERAL)
                ((TestOp::Bits(RA, 0xff, 0x5c), P32), vec![
                    // Load RD from cell pointed to by EP, and add 4 to EP.
                    LoadGlobal(RA, B_EP),
                    Load(P32, RD, Four(RA, Memory::M)),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Add, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_EP), // FIXME: Add check that EP is valid.
                    // Push RD to the stack.
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Root),

                // (LITERAL)I
                ((TestOp::Bits(RA, 0xff, 0x5d), P32), vec![
                    // Push A to the stack.
                    LoadGlobal(RA, B_SP),
                    Constant(P32, RSI, cell_bytes(1)),
                    Binary(Sub, P32, RA, RA, RSI),
                    StoreGlobal(RA, B_SP),
                    LoadGlobal(RD, B_A),
                    Store(RD, Four(RA, Memory::M)),
                ], State::Next),

                // THROW
                ((TestOp::Bits(RA, 0xff, 0x5e), P32), vec![
                    // Set 'BAD to EP
                    LoadGlobal(RA, B_EP),
                    StoreGlobal(RA, Global::Bad),
                    // Load EP from 'THROW
                    LoadGlobal(RA, Global::Throw),
                    Load(P32, RA, Four(RA, Memory::M)),
                    StoreGlobal(RA, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),
            ]},
        }
    }

    fn initial_states(&self) -> Vec<Self::State> {
        vec![State::Root]
    }
}
