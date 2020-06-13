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
        use super::x86_64::{A as EAX, D as EDX, C as ECX, B as EBX, BP as EBP};
        use Address::{EP as B_EP, A as B_A, SP as B_SP, RP as B_RP, Memory};
        match state {
            State::Root => {vec![
                (TestOp::Always, vec![
                    Load(EAX, B_A),
                    Constant(ECX, 8),
                    Binary(Asr, EDX, EAX, ECX),
                    Store(EDX, B_A),
                ], State::Dispatch),
            ]},
            State::Next => {vec![
                (TestOp::Always, vec![
                    Load(EAX, B_EP), // FIXME: Add check that EP is valid.
                    Load(EDX, Memory(EAX)),
                    Store(EDX, B_A),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_EP),
                ], State::Root),
            ]},
            State::Pick => {
                let mut pick = Vec::new();
                for u in 0..4 {
                    pick.push((
                        TestOp::Eq(EDX, u),
                        vec![
                            Load(EAX, B_SP),
                            Constant(ECX, cell_bytes(u + 1)),
                            Binary(Add, EDX, EAX, ECX),
                            Load(EDX, Memory(EDX)),
                            Store(EDX, Memory(EAX)),
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
                        Constant(ECX, cell_bytes(u)),
                        Binary(Add, EBP, EAX, ECX),
                        Load(EBX, Memory(EBP)),
                    ];
                    for v in 0..u {
                        rollu.extend(vec![
                            Constant(ECX, cell_bytes(v)),
                            Binary(Add, ECX, EAX, ECX),
                            Load(EDX, Memory(ECX)),
                            Store(EBX, Memory(ECX)),
                            Move(EBX, EDX),
                        ]);
                    }
                    rollu.extend(vec![
                        Store(EBX, Memory(EBP)),
                    ]);
                    roll.push((
                        TestOp::Eq(EDX, u),
                        rollu,
                        State::Root,
                    ));
                }
                roll
            },
            State::Qdup => {vec![
                (TestOp::Eq(EDX, 0), vec![], State::Root),
                (TestOp::Ne(EDX, 0), vec![
                     Constant(ECX, cell_bytes(1)),
                     Binary(Sub, EAX, EAX, ECX),
                     Store(EDX, Memory(EAX)),
                     Store(EAX, B_SP),
                ], State::Root),
            ]},
            State::Abs => {vec![
                (TestOp::Lt(EDX, 0), vec![
                    Unary(Negate, EDX, EDX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),
                (TestOp::Ge(EDX, 0), vec![], State::Root),
            ]},
            State::Max => {vec![
                (TestOp::Eq(EBX, 0), vec![], State::Root),
                (TestOp::Ne(EBX, 0), vec![
                    Store(EDX, Memory(EAX)),
                ], State::Root),
            ]},
            State::Min => {vec![
                (TestOp::Eq(EBX, 0), vec![], State::Root),
                (TestOp::Ne(EBX, 0), vec![
                    Store(EDX, Memory(EAX)),
                ], State::Root),
            ]},
            State::Lshift => {vec![
                (TestOp::Ult(ECX, CELL_BITS), vec![
                    Binary(Lsl, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),
                (TestOp::Uge(ECX, CELL_BITS), vec![
                    Constant(EDX, 0),
                    Store(EDX, Memory(EAX)),
                ], State::Root),
            ]},
            State::Rshift => {vec![
                (TestOp::Ult(ECX, CELL_BITS), vec![
                    Binary(Lsr, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),
                (TestOp::Uge(ECX, CELL_BITS), vec![
                    Constant(EDX, 0),
                    Store(EDX, Memory(EAX)),
                ], State::Root),
            ]},
            State::Branch => {vec![
                (TestOp::Always, vec![
                    // Load EP from the cell it points to.
                    Load(EAX, B_EP),
                    Load(EAX, Memory(EAX)),
                    Store(EAX, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),
            ]},
            State::Branchi => {vec![
                (TestOp::Always, vec![
                    Load(EAX, B_EP),
                    Load(EDX, B_A),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Mul, EDX, EDX, ECX),
                    Binary(Add, EAX, EAX, EDX),
                    Store(EAX, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),
            ]},
            State::Qbranch => {vec![
                (TestOp::Eq(EDX, 0), vec![], State::Branch),
                (TestOp::Ne(EDX, 0), vec![
                    Load(EAX, B_EP),
                    Constant(EDX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, EDX),
                    Store(EAX, B_EP),
                ], State::Root),
            ]},
            State::Qbranchi => {vec![
                (TestOp::Eq(EDX, 0), vec![], State::Branchi),
                (TestOp::Ne(EDX, 0), vec![], State::Root),
            ]},
            State::Loop => {vec![
                (TestOp::Eq(EBX, 0), vec![
                    // Discard the loop index and limit.
                    Load(EAX, B_RP),
                    Constant(ECX, cell_bytes(2)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_RP),
                    // Add 4 to EP.
                    Load(EAX, B_EP), // FIXME: Add check that EP is valid.
                    Constant(EDX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, EDX),
                    Store(EAX, B_EP),
                ], State::Root),
                (TestOp::Ne(EBX, 0), vec![], State::Branch),
            ]},
            State::Loopi => {vec![
                (TestOp::Eq(EBX, 0), vec![
                    // Discard the loop index and limit.
                    Load(EAX, B_RP),
                    Constant(ECX, cell_bytes(2)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_RP),
                ], State::Root),
                (TestOp::Ne(EBX, 0), vec![], State::Branchi),
            ]},
            State::Ploopp => {vec![
                (TestOp::Lt(EBP, 0), vec![
                    // Discard the loop index and limit.
                    Load(EAX, B_RP),
                    Constant(ECX, cell_bytes(2)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_RP),
                    // Add 4 to EP.
                    Load(EAX, B_EP), // FIXME: Add check that EP is valid.
                    Constant(EDX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, EDX),
                    Store(EAX, B_EP),
                ], State::Root),
                (TestOp::Ge(EBP, 0), vec![], State::Branch),
            ]},
            State::Ploopm => {vec![
                (TestOp::Lt(EBP, 0), vec![
                    // Discard the loop index and limit.
                    Load(EAX, B_RP),
                    Constant(ECX, cell_bytes(2)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_RP),
                    // Add 4 to EP.
                    Load(EAX, B_EP), // FIXME: Add check that EP is valid.
                    Constant(EDX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, EDX),
                    Store(EAX, B_EP),
                ], State::Root),
                (TestOp::Ge(EBP, 0), vec![], State::Branch),
            ]},
            State::Ploop => {vec![
                (TestOp::Ge(EDX, 0), vec![
                    Unary(Not, EBP, EBP),
                    Binary(And, EBP, EBP, EBX),
                ], State::Ploopp),
                (TestOp::Lt(EDX, 0), vec![
                    Unary(Not, EBX, EBX),
                    Binary(And, EBP, EBP, EBX),
                ], State::Ploopm),
            ]},
            State::Ploopip => {vec![
                (TestOp::Lt(EBP, 0), vec![
                    // Discard the loop index and limit.
                    Load(EAX, B_RP),
                    Constant(ECX, cell_bytes(2)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_RP),
                ], State::Root),
                (TestOp::Ge(EBP, 0), vec![], State::Branchi),
            ]},
            State::Ploopim => {vec![
                (TestOp::Lt(EBP, 0), vec![
                    // Discard the loop index and limit.
                    Load(EAX, B_RP),
                    Constant(ECX, cell_bytes(2)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_RP),
                ], State::Root),
                (TestOp::Ge(EBP, 0), vec![], State::Branchi),
            ]},
            State::Ploopi => {vec![
                (TestOp::Ge(EDX, 0), vec![
                    Unary(Not, EBP, EBP),
                    Binary(And, EBP, EBP, EBX),
                ], State::Ploopip),
                (TestOp::Lt(EDX, 0), vec![
                    Unary(Not, EBX, EBX),
                    Binary(And, EBP, EBP, EBX),
                ], State::Ploopim),
            ]},
            State::Dispatch => {vec![
                // NEXT
                (TestOp::Bits(EAX, 0xff, 0x00), vec![], State::Next),

                // DUP
                (TestOp::Bits(EAX, 0xff, 0x01), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // DROP
                (TestOp::Bits(EAX, 0xff, 0x02), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                ], State::Root),

                // SWAP
                (TestOp::Bits(EAX, 0xff, 0x03), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EDX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Load(EBX, Memory(EDX)),
                    Store(ECX, Memory(EDX)),
                    Store(EBX, Memory(EAX)),
                ], State::Root),

                // OVER
                (TestOp::Bits(EAX, 0xff, 0x04), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EDX, EAX, ECX),
                    Load(EBX, Memory(EDX)),
                    Binary(Sub, EAX, EAX, ECX),
                    Store(EBX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // ROT
                (TestOp::Bits(EAX, 0xff, 0x05), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EBP, EAX, ECX),
                    Load(EBX, Memory(EBP)),
                    Store(EDX, Memory(EBP)),
                    Constant(ECX, cell_bytes(2)),
                    Binary(Add, EBP, EAX, ECX),
                    Load(EDX, Memory(EBP)),
                    Store(EBX, Memory(EBP)),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // -ROT
                (TestOp::Bits(EAX, 0xff, 0x06), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(2)),
                    Binary(Add, EBP, EAX, ECX),
                    Load(EBX, Memory(EBP)),
                    Store(EDX, Memory(EBP)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EBP, EAX, ECX),
                    Load(EDX, Memory(EBP)),
                    Store(EBX, Memory(EBP)),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // TUCK
                (TestOp::Bits(EAX, 0xff, 0x07), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EBP, EAX, ECX),
                    Load(EBX, Memory(EBP)),
                    Store(EDX, Memory(EBP)),
                    Store(EBX, Memory(EAX)),
                    Binary(Sub, EAX, EAX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // NIP
                (TestOp::Bits(EAX, 0xff, 0x08), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // PICK
                (TestOp::Bits(EAX, 0xff, 0x09), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                ], State::Pick),

                // ROLL
                (TestOp::Bits(EAX, 0xff, 0x0a), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                ], State::Roll),

                // ?DUP
                (TestOp::Bits(EAX, 0xff, 0x0b), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                ], State::Qdup),

                // >R
                (TestOp::Bits(EAX, 0xff, 0x0c), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                    Load(EAX, B_RP),
                    Binary(Sub, EAX, EAX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_RP),
                ], State::Root),

                // R>
                (TestOp::Bits(EAX, 0xff, 0x0d), vec![
                    Load(EAX, B_RP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_RP),
                    Load(EAX, B_SP),
                    Binary(Sub, EAX, EAX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // R@
                (TestOp::Bits(EAX, 0xff, 0x0e), vec![
                    Load(EAX, B_RP),
                    Load(EDX, Memory(EAX)),
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // <
                (TestOp::Bits(EAX, 0xff, 0x0f), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(Lt, EDX, ECX, EDX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // >
                (TestOp::Bits(EAX, 0xff, 0x10), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(Lt, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // =
                (TestOp::Bits(EAX, 0xff, 0x11), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(Eq, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // <>
                (TestOp::Bits(EAX, 0xff, 0x12), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(Eq, EDX, EDX, ECX),
                    Unary(Not, EDX, EDX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // 0<
                (TestOp::Bits(EAX, 0xff, 0x13), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, 0),
                    Binary(Lt, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // 0>
                (TestOp::Bits(EAX, 0xff, 0x14), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, 0),
                    Binary(Lt, EDX, ECX, EDX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // 0=
                (TestOp::Bits(EAX, 0xff, 0x15), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, 0),
                    Binary(Eq, EDX, ECX, EDX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // 0<>
                (TestOp::Bits(EAX, 0xff, 0x16), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, 0),
                    Binary(Eq, EDX, ECX, EDX),
                    Unary(Not, EDX, EDX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // U<
                (TestOp::Bits(EAX, 0xff, 0x17), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(Ult, EDX, ECX, EDX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // U>
                (TestOp::Bits(EAX, 0xff, 0x18), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(Ult, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // 0
                (TestOp::Bits(EAX, 0xff, 0x19), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Constant(ECX, 0),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // 1
                (TestOp::Bits(EAX, 0xff, 0x1a), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Constant(ECX, 1),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // -1
                (TestOp::Bits(EAX, 0xff, 0x1b), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Constant(ECX, (-Wrapping(1u32)).0),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // CELL
                (TestOp::Bits(EAX, 0xff, 0x1c), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Constant(ECX, cell_bytes(1)),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // -CELL
                (TestOp::Bits(EAX, 0xff, 0x1d), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Constant(ECX, (-Wrapping(cell_bytes(1))).0),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // +
                (TestOp::Bits(EAX, 0xff, 0x1e), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(Add, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // -
                (TestOp::Bits(EAX, 0xff, 0x1f), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(Sub, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // >-<
                (TestOp::Bits(EAX, 0xff, 0x20), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(Sub, EDX, ECX, EDX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // 1+
                (TestOp::Bits(EAX, 0xff, 0x21), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, 1),
                    Binary(Add, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // 1-
                (TestOp::Bits(EAX, 0xff, 0x22), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, 1),
                    Binary(Sub, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // CELL+
                (TestOp::Bits(EAX, 0xff, 0x23), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // CELL-
                (TestOp::Bits(EAX, 0xff, 0x24), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // *
                (TestOp::Bits(EAX, 0xff, 0x25), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(Mul, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // /
                (TestOp::Bits(EAX, 0xff, 0x26), vec![
                    // TODO
                ], State::Root),

                // MOD
                (TestOp::Bits(EAX, 0xff, 0x27), vec![
                    // TODO
                ], State::Root),

                // /MOD
                (TestOp::Bits(EAX, 0xff, 0x28), vec![
                    // TODO
                ], State::Root),

                // U/MOD
                (TestOp::Bits(EAX, 0xff, 0x29), vec![
                    Load(EBX, B_SP),
                    Load(EDX, Memory(EBX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, ECX, EBX, ECX),
                    Load(EAX, Memory(ECX)),
                    Division(UnsignedDivMod, EAX, EDX, EAX, EDX),
                    Store(EDX, Memory(ECX)),
                    Store(EAX, Memory(EBX)),
                ], State::Root),

                // S/REM
                (TestOp::Bits(EAX, 0xff, 0x2a), vec![
                    Load(EBX, B_SP),
                    Load(EDX, Memory(EBX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, ECX, EBX, ECX),
                    Load(EAX, Memory(ECX)),
                    Division(SignedDivMod, EAX, EDX, EAX, EDX),
                    Store(EDX, Memory(ECX)),
                    Store(EAX, Memory(EBX)),
                ], State::Root),

                // 2/
                (TestOp::Bits(EAX, 0xff, 0x2b), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, 1),
                    Binary(Asr, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // CELLS
                (TestOp::Bits(EAX, 0xff, 0x2c), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Mul, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // ABS
                (TestOp::Bits(EAX, 0xff, 0x2d), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                ], State::Abs),

                // NEGATE
                (TestOp::Bits(EAX, 0xff, 0x2e), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Unary(Negate, EDX, EDX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // MAX
                (TestOp::Bits(EAX, 0xff, 0x2f), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                    Load(ECX, Memory(EAX)),
                    Binary(Lt, EBX, ECX, EDX),
                ], State::Max),

                // MIN
                (TestOp::Bits(EAX, 0xff, 0x30), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                    Load(ECX, Memory(EAX)),
                    Binary(Lt, EBX, EDX, ECX),
                ], State::Min),

                // INVERT
                (TestOp::Bits(EAX, 0xff, 0x31), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Unary(Not, EDX, EDX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // AND
                (TestOp::Bits(EAX, 0xff, 0x32), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(And, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // OR
                (TestOp::Bits(EAX, 0xff, 0x33), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(Or, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // XOR
                (TestOp::Bits(EAX, 0xff, 0x34), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Binary(Xor, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // LSHIFT
                (TestOp::Bits(EAX, 0xff, 0x35), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Lshift),

                // RSHIFT
                (TestOp::Bits(EAX, 0xff, 0x36), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Load(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Rshift),

                // 1LSHIFT
                (TestOp::Bits(EAX, 0xff, 0x37), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, 1),
                    Binary(Lsl, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // 1RSHIFT
                (TestOp::Bits(EAX, 0xff, 0x38), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, 1),
                    Binary(Lsr, EDX, EDX, ECX),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // @
                (TestOp::Bits(EAX, 0xff, 0x39), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Load(EDX, Memory(EDX)),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // !
                (TestOp::Bits(EAX, 0xff, 0x3a), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, ECX, EAX, ECX),
                    Load(EBX, Memory(ECX)),
                    Store(EBX, Memory(EDX)),
                    Constant(ECX, cell_bytes(2)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                ], State::Root),

                // C@
                (TestOp::Bits(EAX, 0xff, 0x3b), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    LoadNarrow(Width::One, EDX, Memory(EDX)),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // C!
                (TestOp::Bits(EAX, 0xff, 0x3c), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, ECX, EAX, ECX),
                    Load(EBX, Memory(ECX)),
                    StoreNarrow(Width::One, EBX, Memory(EDX)),
                    Constant(ECX, cell_bytes(2)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                ], State::Root),

                // +!
                (TestOp::Bits(EAX, 0xff, 0x3d), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, ECX, EAX, ECX),
                    Load(EBX, Memory(ECX)),
                    Load(EBP, Memory(EDX)),
                    Binary(Add, EBX, EBP, EBX),
                    Store(EBX, Memory(EDX)),
                    Constant(ECX, cell_bytes(2)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                ], State::Root),

                // SP@
                (TestOp::Bits(EAX, 0xff, 0x3e), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, ECX, EAX, ECX),
                    Store(EAX, Memory(ECX)),
                    Store(ECX, B_SP),
                ], State::Root),

                // SP!
                (TestOp::Bits(EAX, 0xff, 0x3f), vec![
                    Load(EAX, B_SP),
                    Load(EAX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // RP@
                (TestOp::Bits(EAX, 0xff, 0x40), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Load(ECX, B_RP),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // RP!
                (TestOp::Bits(EAX, 0xff, 0x41), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Store(EDX, B_RP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                ], State::Root),

                // EP@
                (TestOp::Bits(EAX, 0xff, 0x42), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Load(ECX, B_EP),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // S0@
                (TestOp::Bits(EAX, 0xff, 0x43), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Load(ECX, Address::S0),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // S0!
                (TestOp::Bits(EAX, 0xff, 0x44), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Store(EDX, Address::S0),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                ], State::Root),

                // R0@
                (TestOp::Bits(EAX, 0xff, 0x45), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Load(ECX, Address::R0),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // R0!
                (TestOp::Bits(EAX, 0xff, 0x46), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Store(EDX, Address::R0),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                ], State::Root),

                // 'THROW@
                (TestOp::Bits(EAX, 0xff, 0x47), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Load(ECX, Address::Throw),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // 'THROW!
                (TestOp::Bits(EAX, 0xff, 0x48), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Store(EDX, Address::Throw),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                ], State::Root),

                // MEMORY@
                (TestOp::Bits(EAX, 0xff, 0x49), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Load(ECX, Address::Memory0),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // 'BAD@
                (TestOp::Bits(EAX, 0xff, 0x4a), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Load(ECX, Address::Bad),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // -ADDRESS@
                (TestOp::Bits(EAX, 0xff, 0x4b), vec![
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Load(ECX, Address::NotAddress),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_SP),
                ], State::Root),

                // BRANCH
                (TestOp::Bits(EAX, 0xff, 0x4c), vec![], State::Branch),

                // BRANCHI
                (TestOp::Bits(EAX, 0xff, 0x4d), vec![], State::Branchi),

                // ?BRANCH
                (TestOp::Bits(EAX, 0xff, 0x4e), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                ], State::Qbranch),

                // ?BRANCHI
                (TestOp::Bits(EAX, 0xff, 0x4f), vec![
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                ], State::Qbranchi),

                // EXECUTE
                (TestOp::Bits(EAX, 0xff, 0x50), vec![
                    // Push EP onto the return stack.
                    Load(EDX, B_RP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EDX, EDX, ECX),
                    Store(EDX, B_RP),
                    Load(EAX, B_EP),
                    Store(EAX, Memory(EDX)),
                    // Put a-addr1 into EP.
                    Load(EDX, B_SP),
                    Load(EAX, Memory(EDX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EDX, EDX, ECX),
                    Store(EDX, B_SP),
                    Store(EAX, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),

                // @EXECUTE
                (TestOp::Bits(EAX, 0xff, 0x51), vec![
                    // Push EP onto the return stack.
                    Load(EDX, B_RP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EDX, EDX, ECX),
                    Store(EDX, B_RP),
                    Load(EAX, B_EP),
                    Store(EAX, Memory(EDX)),
                    // Put the contents of a-addr1 into EP.
                    Load(EDX, B_SP),
                    Load(EAX, Memory(EDX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EDX, EDX, ECX),
                    Store(EDX, B_SP),
                    Load(EAX, Memory(EAX)),
                    Store(EAX, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),

                // CALL
                (TestOp::Bits(EAX, 0xff, 0x52), vec![
                    // Push EP+4 onto the return stack.
                    Load(EDX, B_RP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EDX, EDX, ECX),
                    Store(EDX, B_RP),
                    Load(EAX, B_EP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, Memory(EDX)),
                ], State::Branch),

                // CALLI
                (TestOp::Bits(EAX, 0xff, 0x53), vec![
                    // Push EP onto the return stack.
                    Load(EDX, B_RP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EDX, EDX, ECX),
                    Store(EDX, B_RP),
                    Load(EAX, B_EP),
                    Store(EAX, Memory(EDX)),
                ], State::Branchi),

                // EXIT
                (TestOp::Bits(EAX, 0xff, 0x54), vec![
                    // Put a-addr into EP.
                    Load(EDX, B_RP),
                    Load(EAX, Memory(EDX)),
                    Store(EAX, B_EP), // FIXME: Add check that EP is valid.
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EDX, EDX, ECX),
                    Store(EDX, B_RP),
                ], State::Next),

                // (DO)
                (TestOp::Bits(EAX, 0xff, 0x55), vec![
                    // Pop two items from SP.
                    Load(EAX, B_SP),
                    Load(ECX, Memory(EAX)),
                    Constant(EDX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, EDX),
                    Load(EBX, Memory(EAX)),
                    Binary(Add, EAX, EAX, EDX),
                    Store(EAX, B_SP),
                    // Push two items to RP.
                    Load(EAX, B_RP),
                    Constant(EDX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, EDX),
                    Store(EBX, Memory(EAX)),
                    Binary(Sub, EAX, EAX, EDX),
                    Store(ECX, Memory(EAX)),
                    Store(EAX, B_RP),
                ], State::Root),

                // (LOOP)
                (TestOp::Bits(EAX, 0xff, 0x56), vec![
                    // Load the index and limit from RP.
                    Load(EAX, B_RP),
                    Load(EBX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, ECX, EAX, ECX),
                    Load(ECX, Memory(ECX)),
                    // Update the index.
                    Constant(EDX, 1),
                    Binary(Add, EBX, EBX, EDX),
                    Store(EBX, Memory(EAX)),
                    Binary(Sub, EBX, EBX, ECX),
                ], State::Loop),

                // (LOOP)I
                (TestOp::Bits(EAX, 0xff, 0x57), vec![
                    // Load the index and limit from RP.
                    Load(EAX, B_RP),
                    Load(EBX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, ECX, EAX, ECX),
                    Load(ECX, Memory(ECX)),
                    // Update the index.
                    Constant(EDX, 1),
                    Binary(Add, EBX, EBX, EDX),
                    Store(EBX, Memory(EAX)),
                    Binary(Sub, EBX, EBX, ECX),
                ], State::Loopi),

                // (+LOOP)
                (TestOp::Bits(EAX, 0xff, 0x58), vec![
                    // Pop the step from SP.
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                    // Load the index and limit from RP.
                    Load(EAX, B_RP),
                    Load(EBX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, ECX, EAX, ECX),
                    Load(ECX, Memory(ECX)),
                    // Update the index.
                    Binary(Add, EBP, EBX, EDX),
                    Store(EBP, Memory(EAX)),
                    // Compute the differences between old and new indexes and limit.
                    Binary(Sub, EBX, EBX, ECX),
                    Binary(Sub, EBP, EBP, ECX),
                ], State::Ploop),

                // (+LOOP)I
                (TestOp::Bits(EAX, 0xff, 0x59), vec![
                    // Pop the step from SP.
                    Load(EAX, B_SP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                    // Load the index and limit from RP.
                    Load(EAX, B_RP),
                    Load(EBX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, ECX, EAX, ECX),
                    Load(ECX, Memory(ECX)),
                    // Update the index.
                    Binary(Add, EBP, EBX, EDX),
                    Store(EBP, Memory(EAX)),
                    // Compute the differences between old and new indexes and limit.
                    Binary(Sub, EBX, EBX, ECX),
                    Binary(Sub, EBP, EBP, ECX),
                ], State::Ploopi),

                // UNLOOP
                (TestOp::Bits(EAX, 0xff, 0x5a), vec![
                    // Discard two items from RP.
                    Load(EAX, B_RP),
                    Constant(EDX, cell_bytes(2)),
                    Binary(Add, EAX, EAX, EDX),
                    Store(EAX, B_RP),
                ], State::Root),

                // J
                (TestOp::Bits(EAX, 0xff, 0x5b), vec![
                    // Push the third item of RP to SP.
                    Load(EAX, B_RP),
                    Constant(EDX, cell_bytes(2)),
                    Binary(Add, EAX, EAX, EDX),
                    Load(ECX, Memory(EAX)),
                    Load(EAX, B_SP),
                    Constant(EDX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, EDX),
                    Store(EAX, B_SP),
                    Store(ECX, Memory(EAX)),
                ], State::Root),

                // (LITERAL)
                (TestOp::Bits(EAX, 0xff, 0x5c), vec![
                    // Load EDX from cell pointed to by EP, and add 4 to EP.
                    Load(EAX, B_EP),
                    Load(EDX, Memory(EAX)),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Add, EAX, EAX, ECX),
                    Store(EAX, B_EP), // FIXME: Add check that EP is valid.
                    // Push EDX to the stack.
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                    Store(EDX, Memory(EAX)),
                ], State::Root),

                // (LITERAL)I
                (TestOp::Bits(EAX, 0xff, 0x5d), vec![
                    // Push A to the stack.
                    Load(EAX, B_SP),
                    Constant(ECX, cell_bytes(1)),
                    Binary(Sub, EAX, EAX, ECX),
                    Store(EAX, B_SP),
                    Load(EDX, B_A),
                    Store(EDX, Memory(EAX)),
                ], State::Next),

                // THROW
                (TestOp::Bits(EAX, 0xff, 0x5e), vec![
                    // Set 'BAD to EP
                    Load(EAX, B_EP),
                    Store(EAX, Address::Bad),
                    // Load EP from 'THROW
                    Load(EAX, Address::Throw),
                    Load(EAX, Memory(EAX)),
                    Store(EAX, B_EP), // FIXME: Add check that EP is valid.
                ], State::Next),
            ]},
        }
    }
}
