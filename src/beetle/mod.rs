use std::num::{Wrapping};
use super::control_flow::{Address, State, Machine};
use super::code::{self, Width, Action::*, UnaryOp::*, BinaryOp::*, DivisionOp::*, TestOp};

/** Beetle's address space. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum BeetleAddress {
    Ep,
    A,
    Sp,
    Rp,
    S0,
    R0,
    Throw,
    Bad,
    NotAddress,
    Memory0,
    Memory(code::R),
}

impl Address for BeetleAddress {
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
pub const fn cell_bytes(n: u32) -> Wrapping<u32> { Wrapping(4 * n) }

/** The number of bits in a word. */
pub const CELL_BITS: Wrapping<u32> = cell_bytes(8);

pub type Action = code::Action<BeetleAddress>;

// TODO: Make private.
pub mod decision_tree;

pub fn machine() -> Machine<BeetleAddress> {
    use super::x86_64::{A as EAX, D as EDX, C as ECX, B as EBX, BP as EBP};
    use BeetleAddress::{Ep, A, Sp, Rp, Memory};
    const fn cell_bytes(n: u32) -> Wrapping<u32> { Wrapping(4 * n) }
    const CELL_BITS: Wrapping<u32> = cell_bytes(8);
    // FIXME: Delete.
    struct DecisionTree {
        actions: Vec<Action>,
        tests: Vec<(Test, Box<DecisionTree>)>,
    }
    // FIXME: Delete.
    struct Test {
        register: code::R,
        test_op: TestOp,
        must_be: bool,
    }
    let instructions = vec![
        DecisionTree {
            actions: vec![ // 00 NEXT
                Load(EAX, Ep), // FIXME: Add check that EP is valid.
                Load(EDX, Memory(EAX)),
                Store(EDX, A),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 01 DUP
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 02 DROP
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 03 SWAP
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EDX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Load(EBX, Memory(EDX)),
                Store(ECX, Memory(EDX)),
                Store(EBX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 04 OVER
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EDX, EAX, ECX),
                Load(EBX, Memory(EDX)),
                Binary(Sub, EAX, EAX, ECX),
                Store(EBX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 05 ROT
                Load(EAX, Sp),
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
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 06 -ROT
                Load(EAX, Sp),
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
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 07 TUCK
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EBP, EAX, ECX),
                Load(EBX, Memory(EBP)),
                Store(EDX, Memory(EBP)),
                Store(EBX, Memory(EAX)),
                Binary(Sub, EAX, EAX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 08 NIP
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 09 PICK
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
            ],
            tests: (0..4).map(|u| {
                (
                    Test {
                        register: EDX,
                        test_op: TestOp::Eq(Wrapping(u)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Load(EAX, Sp),
                            Constant(ECX, cell_bytes(u + 1)),
                            Binary(Add, EDX, EAX, ECX),
                            Load(EDX, Memory(EDX)),
                            Store(EDX, Memory(EAX)),
                        ],
                        tests: vec![],
                    }),
                )
            }).collect(),
        },
        DecisionTree {
            actions: vec![ // 0a ROLL
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
            ],
            tests: (0..4).map(|u| {
                (
                    Test {
                        register: EDX,
                        test_op: TestOp::Eq(Wrapping(u)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Constant(ECX, cell_bytes(u)),
                            Binary(Add, EBP, EAX, ECX),
                            Load(EBX, Memory(EBP)),
                        ].into_iter().chain(
                            (0..u).flat_map(|v| {
                                vec![
                                    Constant(ECX, cell_bytes(v)),
                                    Binary(Add, ECX, EAX, ECX),
                                    Load(EDX, Memory(ECX)),
                                    Store(EBX, Memory(ECX)),
                                    Move(EBX, EDX),
                                ]
                            })
                        ).chain(
                            vec![
                                Store(EBX, Memory(EBP)),
                            ]
                        ).collect(),
                        tests: vec![],
                    }),
                )
            }).collect(),
        },
        DecisionTree {
            actions: vec![ // 0b ?DUP
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
            ],
            tests: vec![
                (
                    Test {
                        register: EDX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![],
                        tests: vec![],
                    }),
                ), (
                    Test {
                        register: EDX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Constant(ECX, cell_bytes(1)),
                            Binary(Sub, EAX, EAX, ECX),
                            Store(EDX, Memory(EAX)),
                            Store(EAX, Sp),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 0c >R
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
                Load(EAX, Rp),
                Binary(Sub, EAX, EAX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Rp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 0d R>
                Load(EAX, Rp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Rp),
                Load(EAX, Sp),
                Binary(Sub, EAX, EAX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 0e R@
                Load(EAX, Rp),
                Load(EDX, Memory(EAX)),
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 0f <
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(Lt, EDX, ECX, EDX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 10 >
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(Lt, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 11 =
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(Eq, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 12 <>
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(Eq, EDX, EDX, ECX),
                Unary(Not, EDX, EDX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 13 0<
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, Wrapping(0)),
                Binary(Lt, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 14 0>
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, Wrapping(0)),
                Binary(Lt, EDX, ECX, EDX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 15 0=
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, Wrapping(0)),
                Binary(Eq, EDX, ECX, EDX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 16 0<>
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, Wrapping(0)),
                Binary(Eq, EDX, ECX, EDX),
                Unary(Not, EDX, EDX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 17 U<
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(Ult, EDX, ECX, EDX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 18 U>
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(Ult, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 19 0
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Constant(ECX, Wrapping(0)),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1a 1
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Constant(ECX, Wrapping(1)),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1b -1
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Constant(ECX, -Wrapping(1)),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1c CELL
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Constant(ECX, cell_bytes(1)),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1d -CELL
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Constant(ECX, -cell_bytes(1)),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1e +
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(Add, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1f -
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(Sub, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 20 >-<
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(Sub, EDX, ECX, EDX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 21 1+
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, Wrapping(1)),
                Binary(Add, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 22 1-
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, Wrapping(1)),
                Binary(Sub, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 23 CELL+
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 24 CELL-
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 25 *
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(Mul, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 26 /
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 27 MOD
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 28 /MOD
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 29 U/MOD
                Load(EBX, Sp),
                Load(EDX, Memory(EBX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, ECX, EBX, ECX),
                Load(EAX, Memory(ECX)),
                Division(UnsignedDivMod, EAX, EDX, EAX, EDX),
                Store(EDX, Memory(ECX)),
                Store(EAX, Memory(EBX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2a S/REM
                Load(EBX, Sp),
                Load(EDX, Memory(EBX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, ECX, EBX, ECX),
                Load(EAX, Memory(ECX)),
                Division(SignedDivMod, EAX, EDX, EAX, EDX),
                Store(EDX, Memory(ECX)),
                Store(EAX, Memory(EBX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2b 2/
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, Wrapping(1)),
                Binary(Asr, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2c CELLS
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Mul, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2d ABS
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
            ],
            tests: vec![
                (
                    Test {
                        register: EDX,
                        test_op: TestOp::Lt(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Unary(Negate, EDX, EDX),
                            Store(EDX, Memory(EAX)),
                        ],
                        tests: vec![],
                    }),
                ), (
                    Test {
                        register: EDX,
                        test_op: TestOp::Lt(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 2e NEGATE
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Unary(Negate, EDX, EDX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2f MAX
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
                Load(ECX, Memory(EAX)),
                Binary(Lt, EBX, ECX, EDX),
            ],
            tests: vec![
                (
                    Test {
                        register: EBX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![],
                        tests: vec![],
                    }),
                ), (
                    Test {
                        register: EBX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Store(EDX, Memory(EAX)),
                        ],
                        tests: vec![],
                    }),
                )
            ],
        },
        DecisionTree {
            actions: vec![ // 30 MIN
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
                Load(ECX, Memory(EAX)),
                Binary(Lt, EBX, EDX, ECX),
            ],
            tests: vec![
                (
                    Test {
                        register: EBX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![],
                        tests: vec![],
                    }),
                ), (
                    Test {
                        register: EBX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Store(EDX, Memory(EAX)),
                        ],
                        tests: vec![],
                    }),
                )
            ],
        },
        DecisionTree {
            actions: vec![ // 31 INVERT
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Unary(Not, EDX, EDX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 32 AND
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(And, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 33 OR
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(Or, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 34 XOR
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Binary(Xor, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 35 LSHIFT
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![
                (
                    Test {
                        register: ECX,
                        test_op: TestOp::Ult(CELL_BITS),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Binary(Lsl, EDX, EDX, ECX),
                            Store(EDX, Memory(EAX)),
                        ],
                        tests: vec![],
                    }),
                ), (
                    Test {
                        register: ECX,
                        test_op: TestOp::Ult(CELL_BITS),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Constant(EDX, Wrapping(0)),
                            Store(EDX, Memory(EAX)),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 36 RSHIFT
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Load(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![
                (
                    Test {
                        register: ECX,
                        test_op: TestOp::Ult(CELL_BITS),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Binary(Lsr, EDX, EDX, ECX),
                            Store(EDX, Memory(EAX)),
                        ],
                        tests: vec![],
                    }),
                ), (
                    Test {
                        register: ECX,
                        test_op: TestOp::Ult(CELL_BITS),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Constant(EDX, Wrapping(0)),
                            Store(EDX, Memory(EAX)),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 37 1LSHIFT
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, Wrapping(1)),
                Binary(Lsl, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 38 1RSHIFT
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, Wrapping(1)),
                Binary(Lsr, EDX, EDX, ECX),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 39 @
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Load(EDX, Memory(EDX)),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3a !
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, ECX, EAX, ECX),
                Load(EBX, Memory(ECX)),
                Store(EBX, Memory(EDX)),
                Constant(ECX, cell_bytes(2)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3b C@
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                LoadNarrow(Width::One, EDX, Memory(EDX)),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3c C!
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, ECX, EAX, ECX),
                Load(EBX, Memory(ECX)),
                StoreNarrow(Width::One, EBX, Memory(EDX)),
                Constant(ECX, cell_bytes(2)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3d +!
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, ECX, EAX, ECX),
                Load(EBX, Memory(ECX)),
                Load(EBP, Memory(EDX)),
                Binary(Add, EBX, EBP, EBX),
                Store(EBX, Memory(EDX)),
                Constant(ECX, cell_bytes(2)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3e SP@
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, ECX, EAX, ECX),
                Store(EAX, Memory(ECX)),
                Store(ECX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3f SP!
                Load(EAX, Sp),
                Load(EAX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 40 RP@
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Load(ECX, Rp),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 41 RP!
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Store(EDX, Rp),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 42 EP@
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Load(ECX, Ep),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 43 S0@
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Load(ECX, BeetleAddress::S0),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 44 S0!
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Store(EDX, BeetleAddress::S0),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 45 R0@
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Load(ECX, BeetleAddress::R0),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 46 R0!
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Store(EDX, BeetleAddress::R0),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 47 'THROW@
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Load(ECX, BeetleAddress::Throw),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 48 'THROW!
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Store(EDX, BeetleAddress::Throw),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 49 MEMORY@
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Load(ECX, BeetleAddress::Memory0),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 4a 'BAD@
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Load(ECX, BeetleAddress::Bad),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 4b -ADDRESS@
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Load(ECX, BeetleAddress::NotAddress),
                Store(ECX, Memory(EAX)),
                Store(EAX, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 4c BRANCH
                // Load EP from the cell it points to.
                Load(EAX, Ep),
                Load(EAX, Memory(EAX)),
                Store(EAX, Ep), // FIXME: Add check that EP is valid.
                // NEXT. FIXME: Deduplicate
                Load(EAX, Ep), // FIXME: Add check that EP is valid.
                Load(EDX, Memory(EAX)),
                Store(EDX, A),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 4d BRANCHI
                // Add A*4 to EP.
                Load(EAX, Ep),
                Load(EDX, A),
                Constant(ECX, cell_bytes(1)),
                Binary(Mul, EDX, EDX, ECX),
                Binary(Add, EAX, EAX, EDX),
                Store(EAX, Ep), // FIXME: Add check that EP is valid.
                // NEXT. FIXME: Deduplicate
                Load(EAX, Ep), // FIXME: Add check that EP is valid.
                Load(EDX, Memory(EAX)),
                Store(EDX, A),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 4e ?BRANCH
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
            ],
            tests: vec![
                (
                    Test {
                        register: EDX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            // BRANCH. FIXME: Deduplicate.
                            Load(EAX, Ep),
                            Load(EAX, Memory(EAX)),
                            Store(EAX, Ep), // FIXME: Add check that EP is valid.
                            // NEXT. FIXME: Deduplicate
                            Load(EAX, Ep), // FIXME: Add check that EP is valid.
                            Load(EDX, Memory(EAX)),
                            Store(EDX, A),
                            Constant(ECX, cell_bytes(1)),
                            Binary(Add, EAX, EAX, ECX),
                            Store(EAX, Ep),
                        ],
                        tests: vec![],
                    }),
                ), (
                    Test {
                        register: EDX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Load(EAX, Ep), // FIXME: Add check that EP is valid.
                            Constant(EDX, cell_bytes(1)),
                            Binary(Add, EAX, EAX, EDX),
                            Store(EAX, Ep),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 4f ?BRANCHI
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
            ],
            tests: vec![
                (
                    Test {
                        register: EDX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Load(EAX, Ep),
                            Load(EDX, A),
                            Constant(ECX, cell_bytes(1)),
                            Binary(Mul, EDX, EDX, ECX),
                            Binary(Add, EAX, EAX, EDX),
                            Store(EAX, Ep), // FIXME: Add check that EP is valid.
                            // NEXT. FIXME: Deduplicate
                            Load(EAX, Ep), // FIXME: Add check that EP is valid.
                            Load(EDX, Memory(EAX)),
                            Store(EDX, A),
                            Constant(ECX, cell_bytes(1)),
                            Binary(Add, EAX, EAX, ECX),
                            Store(EAX, Ep),
                        ],
                        tests: vec![],
                    }),
                ), (
                    Test {
                        register: EDX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            // NEXT. FIXME: Deduplicate
                            Load(EAX, Ep), // FIXME: Add check that EP is valid.
                            Load(EDX, Memory(EAX)),
                            Store(EDX, A),
                            Constant(ECX, cell_bytes(1)),
                            Binary(Add, EAX, EAX, ECX),
                            Store(EAX, Ep),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 50 EXECUTE
                // Push EP onto the return stack.
                Load(EDX, Rp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EDX, EDX, ECX),
                Store(EDX, Rp),
                Load(EAX, Ep),
                Store(EAX, Memory(EDX)),
                // Put a-addEDX into EP.
                Load(EDX, Sp),
                Load(EAX, Memory(EDX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EDX, EDX, ECX),
                Store(EDX, Sp),
                Store(EAX, Ep), // FIXME: Add check that EP is valid.
                // NEXT. FIXME: Deduplicate
                Load(EAX, Ep), // FIXME: Add check that EP is valid.
                Load(EDX, Memory(EAX)),
                Store(EDX, A),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 51 @EXECUTE
                // Push EP onto the return stack.
                Load(EDX, Rp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EDX, EDX, ECX),
                Store(EDX, Rp),
                Load(EAX, Ep),
                Store(EAX, Memory(EDX)),
                // Put the contents of a-addEDX into EP.
                Load(EDX, Sp),
                Load(EAX, Memory(EDX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EDX, EDX, ECX),
                Store(EDX, Sp),
                Load(EAX, Memory(EAX)),
                Store(EAX, Ep), // FIXME: Add check that EP is valid.
                // NEXT. FIXME: Deduplicate
                Load(EAX, Ep), // FIXME: Add check that EP is valid.
                Load(EDX, Memory(EAX)),
                Store(EDX, A),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 52 CALL
                // Push EP+4 onto the return stack.
                Load(EDX, Rp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EDX, EDX, ECX),
                Store(EDX, Rp),
                Load(EAX, Ep),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Memory(EDX)),
                // BRANCH. FIXME: Deduplicate
                Load(EAX, Ep),
                Load(EAX, Memory(EAX)),
                Store(EAX, Ep), // FIXME: Add check that EP is valid.
                Load(EAX, Ep), // FIXME: Add check that EP is valid.
                Load(EDX, Memory(EAX)),
                Store(EDX, A),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 53 CALLI
                // Push EP onto the return stack.
                Load(EDX, Rp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EDX, EDX, ECX),
                Store(EDX, Rp),
                Load(EAX, Ep),
                Store(EAX, Memory(EDX)),
                // Add A*4 to EP.
                Load(EAX, Ep),
                Load(EDX, A),
                Constant(ECX, cell_bytes(1)),
                Binary(Mul, EDX, EDX, ECX),
                Binary(Add, EAX, EAX, EDX),
                Store(EAX, Ep), // FIXME: Add check that EP is valid.
                // NEXT. FIXME: Deduplicate
                Load(EAX, Ep), // FIXME: Add check that EP is valid.
                Load(EDX, Memory(EAX)),
                Store(EDX, A),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 54 EXIT
                // Put a-addr into EP.
                Load(EDX, Rp),
                Load(EAX, Memory(EDX)),
                Store(EAX, Ep), // FIXME: Add check that EP is valid.
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EDX, EDX, ECX),
                Store(EDX, Rp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 55 (DO)
                // Pop two items from SP.
                Load(EAX, Sp),
                Load(ECX, Memory(EAX)),
                Constant(EDX, cell_bytes(1)),
                Binary(Add, EAX, EAX, EDX),
                Load(EBX, Memory(EAX)),
                Binary(Add, EAX, EAX, EDX),
                Store(EAX, Sp),
                // Push two items to RP.
                Load(EAX, Rp),
                Constant(EDX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, EDX),
                Store(EBX, Memory(EAX)),
                Binary(Sub, EAX, EAX, EDX),
                Store(ECX, Memory(EAX)),
                Store(EAX, Rp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 56 (LOOP)
                // Load the index and limit from RP.
                Load(EAX, Rp),
                Load(EBX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, ECX, EAX, ECX),
                Load(ECX, Memory(ECX)),
                // Update the index.
                Constant(EDX, Wrapping(1)),
                Binary(Add, EBX, EBX, EDX),
                Store(EBX, Memory(EAX)),
                Binary(Sub, EBX, EBX, ECX),
            ],
            tests: vec![
                (
                    Test {
                        register: EBX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            // Discard the loop index and limit.
                            Load(EAX, Rp),
                            Constant(ECX, cell_bytes(2)),
                            Binary(Add, EAX, EAX, ECX),
                            Store(EAX, Rp),
                            // Add 4 to EP.
                            Load(EAX, Ep), // FIXME: Add check that EP is valid.
                            Constant(EDX, cell_bytes(1)),
                            Binary(Add, EAX, EAX, EDX),
                            Store(EAX, Ep),
                        ],
                        tests: vec![],
                    }),
                ), (
                    Test {
                        register: EBX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            // BRANCH. FIXME: Deduplicate
                            Load(EAX, Ep),
                            Load(EAX, Memory(EAX)),
                            Store(EAX, Ep), // FIXME: Add check that EP is valid.
                            Load(EAX, Ep), // FIXME: Add check that EP is valid.
                            Load(EDX, Memory(EAX)),
                            Store(EDX, A),
                            Constant(ECX, cell_bytes(1)),
                            Binary(Add, EAX, EAX, ECX),
                            Store(EAX, Ep),
                        ],
                        tests: vec![],
                    }),
                )
            ],
        },
        DecisionTree {
            actions: vec![ // 57 (LOOP)I
                // Load the index and limit from RP.
                Load(EAX, Rp),
                Load(EBX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, ECX, EAX, ECX),
                Load(ECX, Memory(ECX)),
                // Update the index.
                Constant(EDX, Wrapping(1)),
                Binary(Add, EBX, EBX, EDX),
                Store(EBX, Memory(EAX)),
                Binary(Sub, EBX, EBX, ECX),
            ],
            tests: vec![
                (
                    Test {
                        register: EBX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            // Discard the loop index and limit.
                            Load(EAX, Rp),
                            Constant(ECX, cell_bytes(2)),
                            Binary(Add, EAX, EAX, ECX),
                            Store(EAX, Rp),
                        ],
                        tests: vec![]
                    }),
                ), (
                    Test {
                        register: EBX,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            // BRANCHI. FIXME: Deduplicate
                            Load(EAX, Ep),
                            Load(EDX, A),
                            Constant(ECX, cell_bytes(1)),
                            Binary(Mul, EDX, EDX, ECX),
                            Binary(Add, EAX, EAX, EDX),
                            Store(EAX, Ep), // FIXME: Add check that EP is valid.
                            Load(EAX, Ep), // FIXME: Add check that EP is valid.
                            Load(EDX, Memory(EAX)),
                            Store(EDX, A),
                            Constant(ECX, cell_bytes(1)),
                            Binary(Add, EAX, EAX, ECX),
                            Store(EAX, Ep),
                        ],
                        tests: vec![],
                    }),
                )
            ],
        },
        DecisionTree { // 58 (+LOOP)
            actions: vec![ //
                // Pop the step from SP.
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
                // Load the index and limit from RP.
                Load(EAX, Rp),
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
            ],
            tests: vec![
                (
                    Test {
                        register: EDX,
                        test_op: TestOp::Lt(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Unary(Not, EBP, EBP),
                            Binary(And, EBP, EBP, EBX),
                        ],
                        tests: vec![
                            (
                                Test {
                                    register: EBP,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: true,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // Discard the loop index and limit.
                                        Load(EAX, Rp),
                                        Constant(ECX, cell_bytes(2)),
                                        Binary(Add, EAX, EAX, ECX),
                                        Store(EAX, Rp),
                                        // Add 4 to EP.
                                        Load(EAX, Ep), // FIXME: Add check that EP is valid.
                                        Constant(EDX, cell_bytes(1)),
                                        Binary(Add, EAX, EAX, EDX),
                                        Store(EAX, Ep),
                                    ],
                                    tests: vec![],
                                }),
                            ),
                            (
                                Test {
                                    register: EBP,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: false,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // BRANCH. FIXME: Deduplicate
                                        Load(EAX, Ep),
                                        Load(EAX, Memory(EAX)),
                                        Store(EAX, Ep), // FIXME: Add check that EP is valid.
                                        Load(EAX, Ep), // FIXME: Add check that EP is valid.
                                        Load(EDX, Memory(EAX)),
                                        Store(EDX, A),
                                        Constant(ECX, cell_bytes(1)),
                                        Binary(Add, EAX, EAX, ECX),
                                        Store(EAX, Ep),
                                    ],
                                    tests: vec![],
                                }),
                            )
                        ]
                    }),
                ),
                (
                    Test {
                        register: EDX,
                        test_op: TestOp::Lt(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Unary(Not, EBX, EBX),
                            Binary(And, EBP, EBP, EBX),
                        ],
                        tests: vec![
                            (
                                Test {
                                    register: EBP,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: true,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // Discard the loop index and limit.
                                        Load(EAX, Rp),
                                        Constant(ECX, cell_bytes(2)),
                                        Binary(Add, EAX, EAX, ECX),
                                        Store(EAX, Rp),
                                        // Add 4 to EP.
                                        Load(EAX, Ep), // FIXME: Add check that EP is valid.
                                        Constant(EDX, cell_bytes(1)),
                                        Binary(Add, EAX, EAX, EDX),
                                        Store(EAX, Ep),
                                    ],
                                    tests: vec![],
                                }),
                            ),
                            (
                                Test {
                                    register: EBP,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: false,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // BRANCH. FIXME: Deduplicate
                                        Load(EAX, Ep),
                                        Load(EAX, Memory(EAX)),
                                        Store(EAX, Ep), // FIXME: Add check that EP is valid.
                                        Load(EAX, Ep), // FIXME: Add check that EP is valid.
                                        Load(EDX, Memory(EAX)),
                                        Store(EDX, A),
                                        Constant(ECX, cell_bytes(1)),
                                        Binary(Add, EAX, EAX, ECX),
                                        Store(EAX, Ep),
                                    ],
                                    tests: vec![],
                                }),
                            )
                        ]
                    }),
                )
            ],
        },
        DecisionTree { // 59 (+LOOP)I
            actions: vec![ //
                // Pop the step from SP.
                Load(EAX, Sp),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Sp),
                // Load the index and limit from RP.
                Load(EAX, Rp),
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
            ],
            tests: vec![
                (
                    Test {
                        register: EDX,
                        test_op: TestOp::Lt(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Unary(Not, EBP, EBP),
                            Binary(And, EBP, EBP, EBX),
                        ],
                        tests: vec![
                            (
                                Test {
                                    register: EBP,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: true,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // Discard the loop index and limit.
                                        Load(EAX, Rp),
                                        Constant(ECX, cell_bytes(2)),
                                        Binary(Add, EAX, EAX, ECX),
                                        Store(EAX, Rp),
                                    ],
                                    tests: vec![],
                                }),
                            ),
                            (
                                Test {
                                    register: EBP,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: false,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // BRANCHI. FIXME: Deduplicate
                                        Load(EAX, Ep),
                                        Load(EDX, A),
                                        Constant(ECX, cell_bytes(1)),
                                        Binary(Mul, EDX, EDX, ECX),
                                        Binary(Add, EAX, EAX, EDX),
                                        Store(EAX, Ep), // FIXME: Add check that EP is valid.
                                        Load(EAX, Ep), // FIXME: Add check that EP is valid.
                                        Load(EDX, Memory(EAX)),
                                        Store(EDX, A),
                                        Constant(ECX, cell_bytes(1)),
                                        Binary(Add, EAX, EAX, ECX),
                                        Store(EAX, Ep),
                                    ],
                                    tests: vec![],
                                }),
                            )
                        ]
                    }),
                ),
                (
                    Test {
                        register: EDX,
                        test_op: TestOp::Lt(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Unary(Not, EBX, EBX),
                            Binary(And, EBP, EBP, EBX),
                        ],
                        tests: vec![
                            (
                                Test {
                                    register: EBP,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: true,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // Discard the loop index and limit.
                                        Load(EAX, Rp),
                                        Constant(ECX, cell_bytes(2)),
                                        Binary(Add, EAX, EAX, ECX),
                                        Store(EAX, Rp),
                                    ],
                                    tests: vec![],
                                }),
                            ),
                            (
                                Test {
                                    register: EBP,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: false,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // BRANCHI. FIXME: Deduplicate
                                        Load(EAX, Ep),
                                        Load(EDX, A),
                                        Constant(ECX, cell_bytes(1)),
                                        Binary(Mul, EDX, EDX, ECX),
                                        Binary(Add, EAX, EAX, EDX),
                                        Store(EAX, Ep), // FIXME: Add check that EP is valid.
                                        Load(EAX, Ep), // FIXME: Add check that EP is valid.
                                        Load(EDX, Memory(EAX)),
                                        Store(EDX, A),
                                        Constant(ECX, cell_bytes(1)),
                                        Binary(Add, EAX, EAX, ECX),
                                        Store(EAX, Ep),
                                    ],
                                    tests: vec![],
                                }),
                            )
                        ]
                    }),
                )
            ],
        },
        DecisionTree {
            actions: vec![ // 5a UNLOOP
                // Discard two items from RP.
                Load(EAX, Rp),
                Constant(EDX, cell_bytes(2)),
                Binary(Add, EAX, EAX, EDX),
                Store(EAX, Rp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 5b J
                // Push the third item of RP to SP.
                Load(EAX, Rp),
                Constant(EDX, cell_bytes(2)),
                Binary(Add, EAX, EAX, EDX),
                Load(ECX, Memory(EAX)),
                Load(EAX, Sp),
                Constant(EDX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, EDX),
                Store(EAX, Sp),
                Store(ECX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 5c (LITERAL)
                // Load EDX from cell pointed to by EP, and add 4 to EP.
                Load(EAX, Ep),
                Load(EDX, Memory(EAX)),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Ep), // FIXME: Add check that EP is valid.
                // Push EDX to the stack.
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Store(EAX, Sp),
                Store(EDX, Memory(EAX)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 5d (LITERAL)I
                // Push A to the stack.
                Load(EAX, Sp),
                Constant(ECX, cell_bytes(1)),
                Binary(Sub, EAX, EAX, ECX),
                Store(EAX, Sp),
                Load(EDX, A),
                Store(EDX, Memory(EAX)),
                // NEXT. FIXME: Deduplicate
                Load(EAX, Ep), // FIXME: Add check that EP is valid.
                Load(EDX, Memory(EAX)),
                Store(EDX, A),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 5e THROW
                // Set 'BAD to EP
                Load(EAX, Ep),
                Store(EAX, BeetleAddress::Bad),
                // Load EP from 'THROW
                Load(EAX, BeetleAddress::Throw),
                Load(EAX, Memory(EAX)),
                Store(EAX, Ep), // FIXME: Add check that EP is valid.
                // NEXT. FIXME: Deduplicate
                Load(EAX, Ep), // FIXME: Add check that EP is valid.
                Load(EDX, Memory(EAX)),
                Store(EDX, A),
                Constant(ECX, cell_bytes(1)),
                Binary(Add, EAX, EAX, ECX),
                Store(EAX, Ep),
            ],
            tests: vec![],
        },
    ];
    // Flatten the tree.
    let states: Vec<State<BeetleAddress>> = vec![];
    /* TODO:
        let root_index = flatten(instructions);
        assert_eq!(root_index, 0);
    */
    // Return the machine.
    Machine {states}
}
