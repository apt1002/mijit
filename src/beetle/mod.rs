use std::num::{Wrapping};
use super::control_flow::{Address, State, Machine};
use super::code::{self, Width, Action, Action::*, UnaryOp::*, BinaryOp::*, DivisionOp::*, TestOp};

/// Beetle's address space.
/// V is the type of a non-compile-time-known variable.
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

pub fn machine() -> Machine<BeetleAddress> {
    use super::x86_64::{A, D, C, B, BP};
    const CELL_BYTES: Wrapping<u32> = Wrapping(4);
    struct DecisionTree {
        actions: Vec<Action<BeetleAddress>>,
        tests: Vec<(code::Test, Box<DecisionTree>)>,
    }
    let instructions = vec![
        DecisionTree {
            actions: vec![ // 00 NEXT
                Load(A, BeetleAddress::Ep),
                Load(D, BeetleAddress::Memory(A)),
                Store(D, BeetleAddress::A),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 01 DUP
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 02 DROP
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 03 SWAP
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Add, D, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Load(B, BeetleAddress::Memory(D)),
                Store(C, BeetleAddress::Memory(D)),
                Store(B, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 04 OVER
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Add, D, A, C),
                Load(B, BeetleAddress::Memory(D)),
                Binary(Sub, A, A, C),
                Store(B, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 05 ROT
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, BP, A, C),
                Load(B, BeetleAddress::Memory(BP)),
                Store(D, BeetleAddress::Memory(BP)),
                Constant(C, CELL_BYTES * Wrapping(2)),
                Binary(Add, BP, A, C),
                Load(D, BeetleAddress::Memory(BP)),
                Store(B, BeetleAddress::Memory(BP)),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 06 -ROT
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES * Wrapping(2)),
                Binary(Add, BP, A, C),
                Load(B, BeetleAddress::Memory(BP)),
                Store(D, BeetleAddress::Memory(BP)),
                Constant(C, CELL_BYTES),
                Binary(Add, BP, A, C),
                Load(D, BeetleAddress::Memory(BP)),
                Store(B, BeetleAddress::Memory(BP)),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 07 TUCK
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, BP, A, C),
                Load(B, BeetleAddress::Memory(BP)),
                Store(D, BeetleAddress::Memory(BP)),
                Store(B, BeetleAddress::Memory(A)),
                Binary(Sub, A, A, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 08 NIP
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 09 PICK
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
            ],
            tests: (0..4).map(|u| {
                (
                    code::Test {
                        register: D,
                        test_op: TestOp::Eq(Wrapping(u)),
                        not: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Load(A, BeetleAddress::Sp),
                            Constant(C, CELL_BYTES * Wrapping(u + 1)),
                            Binary(Add, D, A, C),
                            Load(D, BeetleAddress::Memory(D)),
                            Store(D, BeetleAddress::Memory(A)),
                        ],
                        tests: vec![],
                    })
                )
            }).collect(),
        },
        DecisionTree {
            actions: vec![ // 0a ROLL
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Sp),
            ],
            tests: (0..4).map(|u| {
                (
                    code::Test {
                        register: D,
                        test_op: TestOp::Eq(Wrapping(u)),
                        not: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Constant(C, CELL_BYTES * Wrapping(u)),
                            Binary(Add, BP, A, C),
                            Load(B, BeetleAddress::Memory(BP)),
                        ].into_iter().chain(
                            (0..u).flat_map(|v| {
                                vec![
                                    Constant(C, CELL_BYTES * Wrapping(v)),
                                    Binary(Add, C, A, C),
                                    Load(D, BeetleAddress::Memory(C)),
                                    Store(B, BeetleAddress::Memory(C)),
                                    Move(B, D),
                                ]
                            })
                        ).chain(
                            vec![
                                Store(B, BeetleAddress::Memory(BP)),
                            ]
                        ).collect(),
                        tests: vec![],
                    }),
                )
            }).collect(),
        },
        DecisionTree {
            actions: vec![ // 0b ?DUP
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![
                (
                    code::Test {
                        register: D,
                        test_op: TestOp::Eq(Wrapping(0)),
                        not: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: D,
                        test_op: TestOp::Eq(Wrapping(0)),
                        not: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Constant(C, CELL_BYTES),
                            Binary(Sub, A, A, C),
                            Store(D, BeetleAddress::Memory(A)),
                            Store(A, BeetleAddress::Sp),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 0c >R
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Sp),
                Load(A, BeetleAddress::Rp),
                Binary(Sub, A, A, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Rp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 0d R>
                Load(A, BeetleAddress::Rp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Rp),
                Load(A, BeetleAddress::Sp),
                Binary(Sub, A, A, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 0e R@
                Load(A, BeetleAddress::Rp),
                Load(D, BeetleAddress::Memory(A)),
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 0f <
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Lt, D, C, D),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 10 >
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Lt, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 11 =
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Eq, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 12 <>
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Eq, D, D, C),
                Unary(Not, D, D),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 13 0<
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, Wrapping(0)),
                Binary(Lt, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 14 0>
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, Wrapping(0)),
                Binary(Lt, D, C, D),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 15 0=
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, Wrapping(0)),
                Binary(Eq, D, C, D),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 16 0<>
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, Wrapping(0)),
                Binary(Eq, D, C, D),
                Unary(Not, D, D),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 17 U<
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Ult, D, C, D),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 18 U>
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Ult, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 19 0
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Constant(C, Wrapping(0)),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1a 1
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Constant(C, Wrapping(1)),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1b -1
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Constant(C, -Wrapping(1)),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1c CELL
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Constant(C, CELL_BYTES),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1d -CELL
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Constant(C, -CELL_BYTES),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1e +
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Add, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1f -
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Sub, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 20 >-<
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Sub, D, C, D),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 21 1+
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, Wrapping(1)),
                Binary(Add, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 22 1-
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, Wrapping(1)),
                Binary(Sub, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 23 CELL+
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 24 CELL-
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Sub, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 25 *
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Mul, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
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
                Load(B, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(B)),
                Constant(C, CELL_BYTES),
                Binary(Add, C, B, C),
                Load(A, BeetleAddress::Memory(C)),
                Division(UnsignedDivMod, A, D, A, D),
                Store(D, BeetleAddress::Memory(C)),
                Store(A, BeetleAddress::Memory(B)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2a S/REM
                Load(B, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(B)),
                Constant(C, CELL_BYTES),
                Binary(Add, C, B, C),
                Load(A, BeetleAddress::Memory(C)),
                Division(SignedDivMod, A, D, A, D),
                Store(D, BeetleAddress::Memory(C)),
                Store(A, BeetleAddress::Memory(B)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2b 2/
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, Wrapping(1)),
                Binary(Asr, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2c CELLS
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Mul, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2d ABS
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![
                (
                    code::Test {
                        register: D,
                        test_op: TestOp::Lt(Wrapping(0)),
                        not: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Unary(Negate, D, D),
                            Store(D, BeetleAddress::Memory(A)),
                        ],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: D,
                        test_op: TestOp::Lt(Wrapping(0)),
                        not: true,
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
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Unary(Negate, D, D),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2f MAX
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Sp),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Lt, B, C, D),
            ],
            tests: vec![
                (
                    code::Test {
                        register: B,
                        test_op: TestOp::Eq(Wrapping(0)),
                        not: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: B,
                        test_op: TestOp::Eq(Wrapping(0)),
                        not: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Store(D, BeetleAddress::Memory(A)),
                        ],
                        tests: vec![],
                    }),
                )
            ],
        },
        DecisionTree {
            actions: vec![ // 30 MIN
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Sp),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Lt, B, D, C),
            ],
            tests: vec![
                (
                    code::Test {
                        register: B,
                        test_op: TestOp::Eq(Wrapping(0)),
                        not: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: B,
                        test_op: TestOp::Eq(Wrapping(0)),
                        not: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Store(D, BeetleAddress::Memory(A)),
                        ],
                        tests: vec![],
                    }),
                )
            ],
        },
        DecisionTree {
            actions: vec![ // 31 INVERT
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Unary(Not, D, D),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 32 AND
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(And, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 33 OR
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Or, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 34 XOR
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Binary(Xor, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 35 LSHIFT
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![
                (
                    code::Test {
                        register: C,
                        test_op: TestOp::Ult(CELL_BYTES * Wrapping(8)),
                        not: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Binary(Lsl, D, D, C),
                            Store(D, BeetleAddress::Memory(A)),
                        ],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: C,
                        test_op: TestOp::Ult(CELL_BYTES * Wrapping(8)),
                        not: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Constant(D, Wrapping(0)),
                            Store(D, BeetleAddress::Memory(A)),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 36 RSHIFT
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Load(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![
                (
                    code::Test {
                        register: C,
                        test_op: TestOp::Ult(CELL_BYTES * Wrapping(8)),
                        not: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Binary(Lsr, D, D, C),
                            Store(D, BeetleAddress::Memory(A)),
                        ],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: C,
                        test_op: TestOp::Ult(CELL_BYTES * Wrapping(8)),
                        not: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Constant(D, Wrapping(0)),
                            Store(D, BeetleAddress::Memory(A)),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 37 1LSHIFT
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, Wrapping(1)),
                Binary(Lsl, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 38 1RSHIFT
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, Wrapping(1)),
                Binary(Lsr, D, D, C),
                Store(D, BeetleAddress::Memory(A)),
           ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 39 @
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Load(D, BeetleAddress::Memory(D)),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3a !
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, C, A, C),
                Load(B, BeetleAddress::Memory(C)),
                Store(B, BeetleAddress::Memory(D)),
                Constant(C, CELL_BYTES * Wrapping(2)),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3b C@
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                LoadNarrow(Width::One, D, BeetleAddress::Memory(D)),
                Store(D, BeetleAddress::Memory(A)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3c C!
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, C, A, C),
                Load(B, BeetleAddress::Memory(C)),
                StoreNarrow(Width::One, B, BeetleAddress::Memory(D)),
                Constant(C, CELL_BYTES * Wrapping(2)),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3d +!
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Constant(C, CELL_BYTES),
                Binary(Add, C, A, C),
                Load(B, BeetleAddress::Memory(C)),
                Load(BP, BeetleAddress::Memory(D)),
                Binary(Add, B, BP, B),
                Store(B, BeetleAddress::Memory(D)),
                Constant(C, CELL_BYTES * Wrapping(2)),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3e SP@
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, C, A, C),
                Store(A, BeetleAddress::Memory(C)),
                Store(C, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3f SP!
                Load(A, BeetleAddress::Sp),
                Load(A, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 40 RP@
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Load(C, BeetleAddress::Rp),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 41 RP!
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Store(D, BeetleAddress::Rp),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 42 EP@
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Load(C, BeetleAddress::Ep),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 43 S0@
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Load(C, BeetleAddress::S0),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 44 S0!
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Store(D, BeetleAddress::S0),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 45 R0@
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Load(C, BeetleAddress::R0),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 46 R0!
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Store(D, BeetleAddress::S0),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 47 'THROW@
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Load(C, BeetleAddress::Throw),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 48 'THROW!
                Load(A, BeetleAddress::Sp),
                Load(D, BeetleAddress::Memory(A)),
                Store(D, BeetleAddress::Throw),
                Constant(C, CELL_BYTES),
                Binary(Add, A, A, C),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 49 MEMORY@
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Load(C, BeetleAddress::Memory0),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 4A 'BAD@
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Load(C, BeetleAddress::Bad),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 4B -ADDRESS@
                Load(A, BeetleAddress::Sp),
                Constant(C, CELL_BYTES),
                Binary(Sub, A, A, C),
                Load(C, BeetleAddress::NotAddress),
                Store(C, BeetleAddress::Memory(A)),
                Store(A, BeetleAddress::Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ //
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ //
            ],
            tests: vec![],
        },
    ];
    // Flatten the tree.
    let mut states: Vec<State<BeetleAddress>> = vec![];
    let flatten = |t: DecisionTree| {
        let index = states.len();
        states.push(State {
            actions: t.actions,
            tests: Vec::new(),
        });
        for (condition, t2) in t.tests {
            let if_true = flatten(t2);
            states[index].push(Test {condition, if_true});
        }
    };
    let root_index = flatten(instructions);
    assert_eq!(root_index, 0);
    // Return the machine.
    Machine {states}
}