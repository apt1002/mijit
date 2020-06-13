use std::num::{Wrapping};
use std::rc::{Rc};

use super::{control_flow};
use super::code::{
    self, Width,
    Action::*, UnaryOp::*, BinaryOp::*, DivisionOp::*, TestOp
};

/** Beetle's address space. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum BeetleAddress {
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

impl control_flow::Address for BeetleAddress {
    fn can_alias(&self, other: &Self) -> bool {
        match self {
            &BeetleAddress::Memory(_) => match other {
                &BeetleAddress::Memory(_) => true,
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

pub type Action = code::Action<BeetleAddress>;

// TODO: Make private.
pub mod decision_tree;
use decision_tree::{Block, State};

pub fn machine() -> control_flow::Machine<BeetleAddress> {
    use super::x86_64::{A as EAX, D as EDX, C as ECX, B as EBX, BP as EBP};
    use BeetleAddress::{EP as B_EP, A as B_A, SP as B_SP, RP as B_RP, Memory};

    // The root State. Cases with a `target` of `None` return here.
    let mut root = State::new();
    let mut dispatch = State::new();

    // NEXT
    let mut next = State::new();
    next.add_case(TestOp::Always, Block::new(&[
        Load(EAX, B_EP), // FIXME: Add check that EP is valid.
        Load(EDX, Memory(EAX)),
        Store(EDX, B_A),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_EP),
    ]), None);
    let next = Rc::new(next);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x00), Block::new(&[]), Some(&next));

    // DUP
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x01), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);
    
    // DROP
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x02), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]), None);

    // SWAP
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x03), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EDX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Load(EBX, Memory(EDX)),
        Store(ECX, Memory(EDX)),
        Store(EBX, Memory(EAX)),
    ]), None);

    // OVER
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x04), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EDX, EAX, ECX),
        Load(EBX, Memory(EDX)),
        Binary(Sub, EAX, EAX, ECX),
        Store(EBX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // ROT
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x05), Block::new(&[
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
    ]), None);

    // -ROT
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x06), Block::new(&[
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
    ]), None);

    // TUCK
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x07), Block::new(&[
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
    ]), None);

    // NIP
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x08), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // PICK
    let mut pick = State::new();
    for u in 0..4 {
        pick.add_case(TestOp::Eq(EDX, u), Block::new(&[
            Load(EAX, B_SP),
            Constant(ECX, cell_bytes(u + 1)),
            Binary(Add, EDX, EAX, ECX),
            Load(EDX, Memory(EDX)),
            Store(EDX, Memory(EAX)),
        ]), None);
    }
    let pick = Rc::new(pick);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x09), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
    ]), Some(&pick));

    // ROLL
    let mut roll = State::new();
    for u in 0..4 {
        let mut rollu = Block::new(&[
            Constant(ECX, cell_bytes(u)),
            Binary(Add, EBP, EAX, ECX),
            Load(EBX, Memory(EBP)),
        ]);
        for v in 0..u {
            rollu = rollu.extend(&[
                Constant(ECX, cell_bytes(v)),
                Binary(Add, ECX, EAX, ECX),
                Load(EDX, Memory(ECX)),
                Store(EBX, Memory(ECX)),
                Move(EBX, EDX),
            ])
        }
        rollu = rollu.extend(&[
            Store(EBX, Memory(EBP)),
        ]);
        roll.add_case(TestOp::Eq(EDX, u), rollu, None)
    }
    let roll = Rc::new(roll);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x0a), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]), Some(&roll));

    // ?DUP
    let mut qdup = State::new();
    qdup.add_case(TestOp::Eq(EDX, 0), Block::new(&[
    ]), None);
    qdup.add_case(TestOp::Ne(EDX, 0), Block::new(&[
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);
    let qdup = Rc::new(qdup);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x0b), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
    ]), Some(&qdup));

    // >R
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x0c), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
        Load(EAX, B_RP),
        Binary(Sub, EAX, EAX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_RP),
    ]), None);

    // R>
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x0d), Block::new(&[
        Load(EAX, B_RP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_RP),
        Load(EAX, B_SP),
        Binary(Sub, EAX, EAX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // R@
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x0e), Block::new(&[
        Load(EAX, B_RP),
        Load(EDX, Memory(EAX)),
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // <
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x0f), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Lt, EDX, ECX, EDX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // >
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x10), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Lt, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // =
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x11), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Eq, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // <>
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x12), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Eq, EDX, EDX, ECX),
        Unary(Not, EDX, EDX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // 0<
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x13), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 0),
        Binary(Lt, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // 0>
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x14), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 0),
        Binary(Lt, EDX, ECX, EDX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // 0=
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x15), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 0),
        Binary(Eq, EDX, ECX, EDX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // 0<>
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x16), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 0),
        Binary(Eq, EDX, ECX, EDX),
        Unary(Not, EDX, EDX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // U<
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x17), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Ult, EDX, ECX, EDX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // U>
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x18), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Ult, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // 0
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x19), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Constant(ECX, 0),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // 1
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x1a), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Constant(ECX, 1),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // -1
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x1b), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Constant(ECX, (-Wrapping(1u32)).0),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // CELL
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x1c), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Constant(ECX, cell_bytes(1)),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // -CELL
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x1d), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Constant(ECX, (-Wrapping(cell_bytes(1))).0),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // +
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x1e), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Add, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // -
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x1f), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Sub, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // >-<
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x20), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Sub, EDX, ECX, EDX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // 1+
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x21), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 1),
        Binary(Add, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // 1-
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x22), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 1),
        Binary(Sub, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // CELL+
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x23), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // CELL-
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x24), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // *
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x25), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Mul, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // /
    // dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x26), TODO);
    // MOD
    // dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x27), TODO);
    // /MOD
    // dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x28), TODO);

    // U/MOD
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x29), Block::new(&[
        Load(EBX, B_SP),
        Load(EDX, Memory(EBX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, ECX, EBX, ECX),
        Load(EAX, Memory(ECX)),
        Division(UnsignedDivMod, EAX, EDX, EAX, EDX),
        Store(EDX, Memory(ECX)),
        Store(EAX, Memory(EBX)),
    ]), None);

    // S/REM
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x2a), Block::new(&[
        Load(EBX, B_SP),
        Load(EDX, Memory(EBX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, ECX, EBX, ECX),
        Load(EAX, Memory(ECX)),
        Division(SignedDivMod, EAX, EDX, EAX, EDX),
        Store(EDX, Memory(ECX)),
        Store(EAX, Memory(EBX)),
    ]), None);

    // 2/
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x2b), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 1),
        Binary(Asr, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // CELLS
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x2c), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Mul, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // ABS
    let mut abs = State::new();
    abs.add_case(TestOp::Lt(EDX, 0), Block::new(&[
        Unary(Negate, EDX, EDX),
        Store(EDX, Memory(EAX)),
    ]), None);
    abs.add_case(TestOp::Ge(EDX, 0), Block::new(&[
    ]), None);
    let abs = Rc::new(abs);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x2d), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
    ]), Some(&abs));

    // NEGATE
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x2e), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Unary(Negate, EDX, EDX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // Max
    let mut max = State::new();
    max.add_case(TestOp::Eq(EBX, 0), Block::new(&[
    ]), None);
    max.add_case(TestOp::Ne(EBX, 0), Block::new(&[
        Store(EDX, Memory(EAX)),
    ]), None);
    let max = Rc::new(max);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x2f), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
        Load(ECX, Memory(EAX)),
        Binary(Lt, EBX, ECX, EDX),
    ]), Some(&max));

    // MIN
    let mut min = State::new();
    min.add_case(TestOp::Eq(EBX, 0), Block::new(&[
    ]), None);
    min.add_case(TestOp::Ne(EBX, 0), Block::new(&[
        Store(EDX, Memory(EAX)),
    ]), None);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x30), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
        Load(ECX, Memory(EAX)),
        Binary(Lt, EBX, EDX, ECX),
    ]), None);

    // INVERT
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x31), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Unary(Not, EDX, EDX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // AND
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x32), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(And, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // OR
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x33), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Or, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // XOR
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x34), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Xor, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // LSHIFT
    let mut lshift = State::new();
    lshift.add_case(TestOp::Ult(ECX, CELL_BITS), Block::new(&[
        Binary(Lsl, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]), None);
    lshift.add_case(TestOp::Uge(ECX, CELL_BITS), Block::new(&[
        Constant(EDX, 0),
        Store(EDX, Memory(EAX)),
    ]), None);
    let lshift = Rc::new(lshift);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x35), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), Some(&lshift));

    // RSHIFT
    let mut rshift = State::new();
    rshift.add_case(TestOp::Ult(ECX, CELL_BITS), Block::new(&[
        Binary(Lsr, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]), None);
    rshift.add_case(TestOp::Uge(ECX, CELL_BITS), Block::new(&[
        Constant(EDX, 0),
        Store(EDX, Memory(EAX)),
    ]), None);
    let rshift = Rc::new(rshift);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x36), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), Some(&rshift));

    // 1LSHIFT
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x37), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 1),
        Binary(Lsl, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // 1RSHIFT
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x38), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 1),
        Binary(Lsr, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]), None);

    // @
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x39), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Load(EDX, Memory(EDX)),
        Store(EDX, Memory(EAX)),
    ]), None);

    // !
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x3a), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, ECX, EAX, ECX),
        Load(EBX, Memory(ECX)),
        Store(EBX, Memory(EDX)),
        Constant(ECX, cell_bytes(2)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]), None);

    // C@
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x3b), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        LoadNarrow(Width::One, EDX, Memory(EDX)),
        Store(EDX, Memory(EAX)),
    ]), None);

    // C!
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x3c), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, ECX, EAX, ECX),
        Load(EBX, Memory(ECX)),
        StoreNarrow(Width::One, EBX, Memory(EDX)),
        Constant(ECX, cell_bytes(2)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]), None);

    // +!
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x3d), Block::new(&[
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
    ]), None);

    // SP@
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x3e), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, ECX, EAX, ECX),
        Store(EAX, Memory(ECX)),
        Store(ECX, B_SP),
    ]), None);

    // SP!
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x3f), Block::new(&[
        Load(EAX, B_SP),
        Load(EAX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // RP@
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x40), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, B_RP),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // RP!
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x41), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Store(EDX, B_RP),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]), None);

    // EP@
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x42), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, B_EP),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // S0@
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x43), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, BeetleAddress::S0),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // S0!
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x44), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Store(EDX, BeetleAddress::S0),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]), None);

    // R0@
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x45), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, BeetleAddress::R0),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // R0!
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x46), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Store(EDX, BeetleAddress::R0),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]), None);

    // #THROW@
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x47), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, BeetleAddress::Throw),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // 'THROW!
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x48), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Store(EDX, BeetleAddress::Throw),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]), None);

    // MEMORY@
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x49), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, BeetleAddress::Memory0),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // 'BAD@
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x4a), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, BeetleAddress::Bad),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // -ADDRESS@
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x4b), Block::new(&[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, BeetleAddress::NotAddress),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]), None);

    // BRANCH
    let mut branch = State::new();
    branch.add_case(TestOp::Always, Block::new(&[]), Some(&next));
    let branch = Rc::new(branch);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x4c), Block::new(&[
        // Load EP from the cell it points to.
        Load(EAX, B_EP),
        Load(EAX, Memory(EAX)),
        Store(EAX, B_EP), // FIXME: Add check that EP is valid.
    ]), Some(&branch));

    // BRANCHI
    let mut branchi = State::new();
    branchi.add_case(TestOp::Always, Block::new(&[]), Some(&next));
    let branchi = Rc::new(branchi);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x4d), Block::new(&[
        Load(EAX, B_EP),
        Load(EDX, B_A),
        Constant(ECX, cell_bytes(1)),
        Binary(Mul, EDX, EDX, ECX),
        Binary(Add, EAX, EAX, EDX),
        Store(EAX, B_EP), // FIXME: Add check that EP is valid.
    ]), Some(&branchi));

    // ?BRANCH
    let mut qbranch = State::new();
    qbranch.add_case(TestOp::Eq(EDX, 0), Block::new(&[]), Some(&branch));
    qbranch.add_case(TestOp::Ne(EDX, 0), Block::new(&[
        Load(EAX, B_EP),
        Constant(EDX, cell_bytes(1)),
        Binary(Add, EAX, EAX, EDX),
        Store(EAX, B_EP),
    ]), None);
    let qbranch = Rc::new(qbranch);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x4e), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]), Some(&qbranch));

    // ?BRANCHI
    let mut qbranchi = State::new();
    qbranchi.add_case(TestOp::Eq(EDX, 0), Block::new(&[]), Some(&branchi));
    qbranchi.add_case(TestOp::Ne(EDX, 0), Block::new(&[]), None);
    let qbranchi = Rc::new(qbranchi);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x4f), Block::new(&[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]), Some(&qbranchi));

    // EXECUTE
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x50), Block::new(&[
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
    ]), Some(&next));

    // @EXECUTE
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x51), Block::new(&[
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
    ]), Some(&next));

    // CALL
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x52), Block::new(&[
        // Push EP+4 onto the return stack.
        Load(EDX, B_RP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EDX, EDX, ECX),
        Store(EDX, B_RP),
        Load(EAX, B_EP),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, Memory(EDX)),
    ]), Some(&branch));

    // CALLI
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x53), Block::new(&[
        // Push EP onto the return stack.
        Load(EDX, B_RP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EDX, EDX, ECX),
        Store(EDX, B_RP),
        Load(EAX, B_EP),
        Store(EAX, Memory(EDX)),
    ]), Some(&branchi));

    // EXIT
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x54), Block::new(&[
        // Put a-addr into EP.
        Load(EDX, B_RP),
        Load(EAX, Memory(EDX)),
        Store(EAX, B_EP), // FIXME: Add check that EP is valid.
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EDX, EDX, ECX),
        Store(EDX, B_RP),
    ]), Some(&next));

    // (DO)
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x55), Block::new(&[
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
    ]), None);

    // (LOOP)
    let mut loop_ = State::new();
    loop_.add_case(TestOp::Eq(EBX, 0), Block::new(&[
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
    ]), None);
    loop_.add_case(TestOp::Ne(EBX, 0), Block::new(&[]), Some(&branch));
    let loop_ = Rc::new(loop_);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x56), Block::new(&[
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
    ]), Some(&loop_));

    // (LOOP)I
    let mut loopi = State::new();
    loopi.add_case(TestOp::Eq(EBX, 0), Block::new(&[
        // Discard the loop index and limit.
        Load(EAX, B_RP),
        Constant(ECX, cell_bytes(2)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_RP),
    ]), None);
    loopi.add_case(TestOp::Ne(EBX, 0), Block::new(&[]), Some(&branchi));
    let loopi = Rc::new(loopi);
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x57), Block::new(&[
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
    ]), Some(&loopi));

    // (+LOOP)
    let mut ploopp = State::new();
    ploopp.add_case(TestOp::Lt(EBP, 0), Block::new(&[
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
    ]), None);
    ploopp.add_case(TestOp::Ge(EBP, 0), Block::new(&[]), Some(&branch));
    let ploopp = Rc::new(ploopp);

    let mut ploopm = State::new();
    ploopm.add_case(TestOp::Lt(EBP, 0), Block::new(&[
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
    ]), None);
    ploopm.add_case(TestOp::Ge(EBP, 0), Block::new(&[]), Some(&branch));
    let ploopm = Rc::new(ploopm);

    let mut ploop = State::new();
    ploop.add_case(TestOp::Ge(EDX, 0), Block::new(&[
        Unary(Not, EBP, EBP),
        Binary(And, EBP, EBP, EBX),
    ]), Some(&ploopp));
    ploop.add_case(TestOp::Lt(EDX, 0), Block::new(&[
        Unary(Not, EBX, EBX),
        Binary(And, EBP, EBP, EBX),
    ]), Some(&ploopm));
    let ploop = Rc::new(ploop);

    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x58), Block::new(&[
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
    ]), Some(&ploop));

    // (+LOOP)I
    let mut ploopip = State::new();
    ploopip.add_case(TestOp::Lt(EBP, 0), Block::new(&[
        // Discard the loop index and limit.
        Load(EAX, B_RP),
        Constant(ECX, cell_bytes(2)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_RP),
    ]), None);
    ploopip.add_case(TestOp::Ge(EBP, 0), Block::new(&[]), Some(&branchi));
    let ploopip = Rc::new(ploopip);

    let mut ploopim = State::new();
    ploopim.add_case(TestOp::Lt(EBP, 0), Block::new(&[
        // Discard the loop index and limit.
        Load(EAX, B_RP),
        Constant(ECX, cell_bytes(2)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_RP),
    ]), None);
    ploopim.add_case(TestOp::Ge(EBP, 0), Block::new(&[]), Some(&branchi));
    let ploopim = Rc::new(ploopim);

    let mut ploopi = State::new();
    ploopi.add_case(TestOp::Ge(EDX, 0), Block::new(&[
        Unary(Not, EBP, EBP),
        Binary(And, EBP, EBP, EBX),
    ]), Some(&ploopip));
    ploopi.add_case(TestOp::Lt(EDX, 0), Block::new(&[  
        Unary(Not, EBX, EBX),
        Binary(And, EBP, EBP, EBX),
    ]), Some(&ploopim));
    let ploopi = Rc::new(ploopi);

    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x59), Block::new(&[
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
    ]), Some(&ploopi));

    // UNLOOP
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x5a), Block::new(&[
        // Discard two items from RP.
        Load(EAX, B_RP),
        Constant(EDX, cell_bytes(2)),
        Binary(Add, EAX, EAX, EDX),
        Store(EAX, B_RP),
    ]), None);

    // J
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x5b), Block::new(&[
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
    ]), None);

    // (LITERAL)
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x5c), Block::new(&[
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
    ]), None);

    // (LITERAL)I
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x5d), Block::new(&[
        // Push A to the stack.
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Store(EAX, B_SP),
        Load(EDX, B_A),
        Store(EDX, Memory(EAX)),
    ]), Some(&next));

    // THROW
    dispatch.add_case(TestOp::Bits(EAX, 0xff, 0x5e), Block::new(&[
        // Set 'BAD to EP
        Load(EAX, B_EP),
        Store(EAX, BeetleAddress::Bad),
        // Load EP from 'THROW
        Load(EAX, BeetleAddress::Throw),
        Load(EAX, Memory(EAX)),
        Store(EAX, B_EP), // FIXME: Add check that EP is valid.
    ]), Some(&next));

    // Finalize dispatch.
    let dispatch = Rc::new(dispatch);
    root.add_case(TestOp::Always, Block::new(&[
        Load(EAX, B_A),
        Constant(ECX, 8),
        Binary(Asr, EDX, EAX, ECX),
        Store(EDX, B_A),
    ]), Some(&dispatch));

    // Flatten the tree.
    let states: Vec<control_flow::State<BeetleAddress>> = vec![];
    /* TODO:
        let root_index = flatten(instructions);
        assert_eq!(root_index, 0);
    */
    // Return the machine.
    control_flow::Machine {states}
}
