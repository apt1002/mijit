use std::num::{Wrapping};

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
use decision_tree::{Block};

pub fn machine() -> control_flow::Machine<BeetleAddress> {
    use super::x86_64::{A as EAX, D as EDX, C as ECX, B as EBX, BP as EBP};
    use BeetleAddress::{EP as B_EP, A as B_A, SP as B_SP, RP as B_RP, Memory};

    // The root State. Cases with a `target` of `None` return here.
    let mut root = Vec::new();
    let mut dispatch = Vec::new();

    // NEXT
    let mut next = Vec::new();
    next.push(Block::new(TestOp::Always, &[
        Load(EAX, B_EP), // FIXME: Add check that EP is valid.
        Load(EDX, Memory(EAX)),
        Store(EDX, B_A),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_EP),
    ]).to_case(None));
    let next = next.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x00), &[]).to_case(Some(&next)));

    // DUP
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x01), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));
    
    // DROP
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x02), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]).to_case(None));

    // SWAP
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x03), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EDX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Load(EBX, Memory(EDX)),
        Store(ECX, Memory(EDX)),
        Store(EBX, Memory(EAX)),
    ]).to_case(None));

    // OVER
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x04), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EDX, EAX, ECX),
        Load(EBX, Memory(EDX)),
        Binary(Sub, EAX, EAX, ECX),
        Store(EBX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // ROT
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x05), &[
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
    ]).to_case(None));

    // -ROT
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x06), &[
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
    ]).to_case(None));

    // TUCK
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x07), &[
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
    ]).to_case(None));

    // NIP
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x08), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // PICK
    let mut pick = Vec::new();
    for u in 0..4 {
        pick.push(Block::new(TestOp::Eq(EDX, u), &[
            Load(EAX, B_SP),
            Constant(ECX, cell_bytes(u + 1)),
            Binary(Add, EDX, EAX, ECX),
            Load(EDX, Memory(EDX)),
            Store(EDX, Memory(EAX)),
        ]).to_case(None));
    }
    let pick = pick.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x09), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
    ]).to_case(Some(&pick)));

    // ROLL
    let mut roll = Vec::new();
    for u in 0..4 {
        let mut rollu = Block::new(TestOp::Eq(EDX, u), &[
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
        roll.push(rollu.to_case(None))
    }
    let roll = roll.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x0a), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]).to_case(Some(&roll)));

    // ?DUP
    let mut qdup = Vec::new();
    qdup.push(Block::new(TestOp::Eq(EDX, 0), &[]).to_case(None));
    qdup.push(Block::new(TestOp::Ne(EDX, 0), &[
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));
    let qdup = qdup.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x0b), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
    ]).to_case(Some(&qdup)));

    // >R
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x0c), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
        Load(EAX, B_RP),
        Binary(Sub, EAX, EAX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_RP),
    ]).to_case(None));

    // R>
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x0d), &[
        Load(EAX, B_RP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_RP),
        Load(EAX, B_SP),
        Binary(Sub, EAX, EAX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // R@
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x0e), &[
        Load(EAX, B_RP),
        Load(EDX, Memory(EAX)),
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // <
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x0f), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Lt, EDX, ECX, EDX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // >
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x10), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Lt, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // =
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x11), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Eq, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // <>
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x12), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Eq, EDX, EDX, ECX),
        Unary(Not, EDX, EDX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // 0<
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x13), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 0),
        Binary(Lt, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // 0>
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x14), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 0),
        Binary(Lt, EDX, ECX, EDX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // 0=
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x15), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 0),
        Binary(Eq, EDX, ECX, EDX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // 0<>
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x16), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 0),
        Binary(Eq, EDX, ECX, EDX),
        Unary(Not, EDX, EDX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // U<
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x17), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Ult, EDX, ECX, EDX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // U>
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x18), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Ult, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // 0
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x19), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Constant(ECX, 0),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // 1
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x1a), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Constant(ECX, 1),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // -1
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x1b), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Constant(ECX, (-Wrapping(1u32)).0),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // CELL
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x1c), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Constant(ECX, cell_bytes(1)),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // -CELL
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x1d), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Constant(ECX, (-Wrapping(cell_bytes(1))).0),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // +
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x1e), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Add, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // -
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x1f), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Sub, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // >-<
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x20), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Sub, EDX, ECX, EDX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // 1+
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x21), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 1),
        Binary(Add, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // 1-
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x22), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 1),
        Binary(Sub, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // CELL+
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x23), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // CELL-
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x24), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // *
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x25), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Mul, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // /
    // dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x26), TODO));
    // MOD
    // dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x27), TODO));
    // /MOD
    // dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x28), TODO));

    // U/MOD
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x29), &[
        Load(EBX, B_SP),
        Load(EDX, Memory(EBX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, ECX, EBX, ECX),
        Load(EAX, Memory(ECX)),
        Division(UnsignedDivMod, EAX, EDX, EAX, EDX),
        Store(EDX, Memory(ECX)),
        Store(EAX, Memory(EBX)),
    ]).to_case(None));

    // S/REM
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x2a), &[
        Load(EBX, B_SP),
        Load(EDX, Memory(EBX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, ECX, EBX, ECX),
        Load(EAX, Memory(ECX)),
        Division(SignedDivMod, EAX, EDX, EAX, EDX),
        Store(EDX, Memory(ECX)),
        Store(EAX, Memory(EBX)),
    ]).to_case(None));

    // 2/
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x2b), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 1),
        Binary(Asr, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // CELLS
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x2c), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Mul, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // ABS
    let mut abs = Vec::new();
    abs.push(Block::new(TestOp::Lt(EDX, 0), &[
        Unary(Negate, EDX, EDX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));
    abs.push(Block::new(TestOp::Ge(EDX, 0), &[]).to_case(None));
    let abs = abs.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x2d), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
    ]).to_case(Some(&abs)));

    // NEGATE
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x2e), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Unary(Negate, EDX, EDX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // Max
    let mut max = Vec::new();
    max.push(Block::new(TestOp::Eq(EBX, 0), &[]).to_case(None));
    max.push(Block::new(TestOp::Ne(EBX, 0), &[
        Store(EDX, Memory(EAX)),
    ]).to_case(None));
    let max = max.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x2f), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
        Load(ECX, Memory(EAX)),
        Binary(Lt, EBX, ECX, EDX),
    ]).to_case(Some(&max)));

    // MIN
    let mut min = Vec::new();
    min.push(Block::new(TestOp::Eq(EBX, 0), &[]).to_case(None));
    min.push(Block::new(TestOp::Ne(EBX, 0), &[
        Store(EDX, Memory(EAX)),
    ]).to_case(None));
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x30), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
        Load(ECX, Memory(EAX)),
        Binary(Lt, EBX, EDX, ECX),
    ]).to_case(None));

    // INVERT
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x31), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Unary(Not, EDX, EDX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // AND
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x32), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(And, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // OR
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x33), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Or, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // XOR
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x34), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Binary(Xor, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // LSHIFT
    let mut lshift = Vec::new();
    lshift.push(Block::new(TestOp::Ult(ECX, CELL_BITS), &[
        Binary(Lsl, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));
    lshift.push(Block::new(TestOp::Uge(ECX, CELL_BITS), &[
        Constant(EDX, 0),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));
    let lshift = lshift.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x35), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(Some(&lshift)));

    // RSHIFT
    let mut rshift = Vec::new();
    rshift.push(Block::new(TestOp::Ult(ECX, CELL_BITS), &[
        Binary(Lsr, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));
    rshift.push(Block::new(TestOp::Uge(ECX, CELL_BITS), &[
        Constant(EDX, 0),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));
    let rshift = rshift.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x36), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Load(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(Some(&rshift)));

    // 1LSHIFT
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x37), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 1),
        Binary(Lsl, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // 1RSHIFT
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x38), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, 1),
        Binary(Lsr, EDX, EDX, ECX),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // @
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x39), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Load(EDX, Memory(EDX)),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // !
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x3a), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, ECX, EAX, ECX),
        Load(EBX, Memory(ECX)),
        Store(EBX, Memory(EDX)),
        Constant(ECX, cell_bytes(2)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]).to_case(None));

    // C@
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x3b), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        LoadNarrow(Width::One, EDX, Memory(EDX)),
        Store(EDX, Memory(EAX)),
    ]).to_case(None));

    // C!
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x3c), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, ECX, EAX, ECX),
        Load(EBX, Memory(ECX)),
        StoreNarrow(Width::One, EBX, Memory(EDX)),
        Constant(ECX, cell_bytes(2)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]).to_case(None));

    // +!
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x3d), &[
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
    ]).to_case(None));

    // SP@
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x3e), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, ECX, EAX, ECX),
        Store(EAX, Memory(ECX)),
        Store(ECX, B_SP),
    ]).to_case(None));

    // SP!
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x3f), &[
        Load(EAX, B_SP),
        Load(EAX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // RP@
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x40), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, B_RP),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // RP!
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x41), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Store(EDX, B_RP),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]).to_case(None));

    // EP@
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x42), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, B_EP),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // S0@
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x43), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, BeetleAddress::S0),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // S0!
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x44), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Store(EDX, BeetleAddress::S0),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]).to_case(None));

    // R0@
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x45), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, BeetleAddress::R0),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // R0!
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x46), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Store(EDX, BeetleAddress::R0),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]).to_case(None));

    // 'THROW@
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x47), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, BeetleAddress::Throw),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // 'THROW!
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x48), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Store(EDX, BeetleAddress::Throw),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]).to_case(None));

    // MEMORY@
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x49), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, BeetleAddress::Memory0),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // 'BAD@
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x4a), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, BeetleAddress::Bad),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // -ADDRESS@
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x4b), &[
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Load(ECX, BeetleAddress::NotAddress),
        Store(ECX, Memory(EAX)),
        Store(EAX, B_SP),
    ]).to_case(None));

    // BRANCH
    let mut branch = Vec::new();
    branch.push(Block::new(TestOp::Always, &[]).to_case(Some(&next)));
    let branch = branch.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x4c), &[
        // Load EP from the cell it points to.
        Load(EAX, B_EP),
        Load(EAX, Memory(EAX)),
        Store(EAX, B_EP), // FIXME: Add check that EP is valid.
    ]).to_case(Some(&branch)));

    // BRANCHI
    let mut branchi = Vec::new();
    branchi.push(Block::new(TestOp::Always, &[]).to_case(Some(&next)));
    let branchi = branchi.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x4d), &[
        Load(EAX, B_EP),
        Load(EDX, B_A),
        Constant(ECX, cell_bytes(1)),
        Binary(Mul, EDX, EDX, ECX),
        Binary(Add, EAX, EAX, EDX),
        Store(EAX, B_EP), // FIXME: Add check that EP is valid.
    ]).to_case(Some(&branchi)));

    // ?BRANCH
    let mut qbranch = Vec::new();
    qbranch.push(Block::new(TestOp::Eq(EDX, 0), &[]).to_case(Some(&branch)));
    qbranch.push(Block::new(TestOp::Ne(EDX, 0), &[
        Load(EAX, B_EP),
        Constant(EDX, cell_bytes(1)),
        Binary(Add, EAX, EAX, EDX),
        Store(EAX, B_EP),
    ]).to_case(None));
    let qbranch = qbranch.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x4e), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]).to_case(Some(&qbranch)));

    // ?BRANCHI
    let mut qbranchi = Vec::new();
    qbranchi.push(Block::new(TestOp::Eq(EDX, 0), &[]).to_case(Some(&branchi)));
    qbranchi.push(Block::new(TestOp::Ne(EDX, 0), &[]).to_case(None));
    let qbranchi = qbranchi.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x4f), &[
        Load(EAX, B_SP),
        Load(EDX, Memory(EAX)),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_SP),
    ]).to_case(Some(&qbranchi)));

    // EXECUTE
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x50), &[
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
    ]).to_case(Some(&next)));

    // @EXECUTE
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x51), &[
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
    ]).to_case(Some(&next)));

    // CALL
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x52), &[
        // Push EP+4 onto the return stack.
        Load(EDX, B_RP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EDX, EDX, ECX),
        Store(EDX, B_RP),
        Load(EAX, B_EP),
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, Memory(EDX)),
    ]).to_case(Some(&branch)));

    // CALLI
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x53), &[
        // Push EP onto the return stack.
        Load(EDX, B_RP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EDX, EDX, ECX),
        Store(EDX, B_RP),
        Load(EAX, B_EP),
        Store(EAX, Memory(EDX)),
    ]).to_case(Some(&branchi)));

    // EXIT
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x54), &[
        // Put a-addr into EP.
        Load(EDX, B_RP),
        Load(EAX, Memory(EDX)),
        Store(EAX, B_EP), // FIXME: Add check that EP is valid.
        Constant(ECX, cell_bytes(1)),
        Binary(Add, EDX, EDX, ECX),
        Store(EDX, B_RP),
    ]).to_case(Some(&next)));

    // (DO)
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x55), &[
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
    ]).to_case(None));

    // (LOOP)
    let mut loop_ = Vec::new();
    loop_.push(Block::new(TestOp::Eq(EBX, 0), &[
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
    ]).to_case(None));
    loop_.push(Block::new(TestOp::Ne(EBX, 0), &[]).to_case(Some(&branch)));
    let loop_ = loop_.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x56), &[
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
    ]).to_case(Some(&loop_)));

    // (LOOP)I
    let mut loopi = Vec::new();
    loopi.push(Block::new(TestOp::Eq(EBX, 0), &[
        // Discard the loop index and limit.
        Load(EAX, B_RP),
        Constant(ECX, cell_bytes(2)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_RP),
    ]).to_case(None));
    loopi.push(Block::new(TestOp::Ne(EBX, 0), &[]).to_case(Some(&branchi)));
    let loopi = loopi.into();
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x57), &[
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
    ]).to_case(Some(&loopi)));

    // (+LOOP)
    let mut ploopp = Vec::new();
    ploopp.push(Block::new(TestOp::Lt(EBP, 0), &[
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
    ]).to_case(None));
    ploopp.push(Block::new(TestOp::Ge(EBP, 0), &[]).to_case(Some(&branch)));
    let ploopp = ploopp.into();

    let mut ploopm = Vec::new();
    ploopm.push(Block::new(TestOp::Lt(EBP, 0), &[
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
    ]).to_case(None));
    ploopm.push(Block::new(TestOp::Ge(EBP, 0), &[]).to_case(Some(&branch)));
    let ploopm = ploopm.into();

    let mut ploop = Vec::new();
    ploop.push(Block::new(TestOp::Ge(EDX, 0), &[
        Unary(Not, EBP, EBP),
        Binary(And, EBP, EBP, EBX),
    ]).to_case(Some(&ploopp)));
    ploop.push(Block::new(TestOp::Lt(EDX, 0), &[
        Unary(Not, EBX, EBX),
        Binary(And, EBP, EBP, EBX),
    ]).to_case(Some(&ploopm)));
    let ploop = ploop.into();

    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x58), &[
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
    ]).to_case(Some(&ploop)));

    // (+LOOP)I
    let mut ploopip = Vec::new();
    ploopip.push(Block::new(TestOp::Lt(EBP, 0), &[
        // Discard the loop index and limit.
        Load(EAX, B_RP),
        Constant(ECX, cell_bytes(2)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_RP),
    ]).to_case(None));
    ploopip.push(Block::new(TestOp::Ge(EBP, 0), &[]).to_case(Some(&branchi)));
    let ploopip = ploopip.into();

    let mut ploopim = Vec::new();
    ploopim.push(Block::new(TestOp::Lt(EBP, 0), &[
        // Discard the loop index and limit.
        Load(EAX, B_RP),
        Constant(ECX, cell_bytes(2)),
        Binary(Add, EAX, EAX, ECX),
        Store(EAX, B_RP),
    ]).to_case(None));
    ploopim.push(Block::new(TestOp::Ge(EBP, 0), &[]).to_case(Some(&branchi)));
    let ploopim = ploopim.into();

    let mut ploopi = Vec::new();
    ploopi.push(Block::new(TestOp::Ge(EDX, 0), &[
        Unary(Not, EBP, EBP),
        Binary(And, EBP, EBP, EBX),
    ]).to_case(Some(&ploopip)));
    ploopi.push(Block::new(TestOp::Lt(EDX, 0), &[
        Unary(Not, EBX, EBX),
        Binary(And, EBP, EBP, EBX),
    ]).to_case(Some(&ploopim)));
    let ploopi = ploopi.into();

    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x59), &[
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
    ]).to_case(Some(&ploopi)));

    // UNLOOP
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x5a), &[
        // Discard two items from RP.
        Load(EAX, B_RP),
        Constant(EDX, cell_bytes(2)),
        Binary(Add, EAX, EAX, EDX),
        Store(EAX, B_RP),
    ]).to_case(None));

    // J
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x5b), &[
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
    ]).to_case(None));

    // (LITERAL)
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x5c), &[
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
    ]).to_case(None));

    // (LITERAL)I
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x5d), &[
        // Push A to the stack.
        Load(EAX, B_SP),
        Constant(ECX, cell_bytes(1)),
        Binary(Sub, EAX, EAX, ECX),
        Store(EAX, B_SP),
        Load(EDX, B_A),
        Store(EDX, Memory(EAX)),
    ]).to_case(Some(&next)));

    // THROW
    dispatch.push(Block::new(TestOp::Bits(EAX, 0xff, 0x5e), &[
        // Set 'BAD to EP
        Load(EAX, B_EP),
        Store(EAX, BeetleAddress::Bad),
        // Load EP from 'THROW
        Load(EAX, BeetleAddress::Throw),
        Load(EAX, Memory(EAX)),
        Store(EAX, B_EP), // FIXME: Add check that EP is valid.
    ]).to_case(Some(&next)));

    // Finalize dispatch.
    let dispatch = dispatch.into();
    root.push(Block::new(TestOp::Always, &[
        Load(EAX, B_A),
        Constant(ECX, 8),
        Binary(Asr, EDX, EAX, ECX),
        Store(EDX, B_A),
    ]).to_case(Some(&dispatch)));

    // Flatten the tree.
    let states: Vec<control_flow::State<BeetleAddress>> = vec![];
    /* TODO:
        let root_index = flatten(instructions);
        assert_eq!(root_index, 0);
    */
    // Return the machine.
    control_flow::Machine {states}
}
