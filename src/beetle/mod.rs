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
    use super::x86_64::{A as R0, D as R1, C as R2, B as R3, BP as R4};
    use BeetleAddress::{Ep, A, Sp, Rp, Memory};
    const fn cell_bytes(n: u32) -> Wrapping<u32> { Wrapping(4 * n) }
    const CELL_BITS: Wrapping<u32> = cell_bytes(8);
    struct DecisionTree {
        actions: Vec<Action<BeetleAddress>>,
        tests: Vec<(code::Test, Box<DecisionTree>)>,
    }
    let instructions = vec![
        DecisionTree {
            actions: vec![ // 00 NEXT
                Load(R0, Ep), // FIXME: Add check that EP is valid.
                Load(R1, Memory(R0)),
                Store(R1, A),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 01 DUP
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 02 DROP
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 03 SWAP
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R1, R0, R2),
                Load(R2, Memory(R0)),
                Load(R3, Memory(R1)),
                Store(R2, Memory(R1)),
                Store(R3, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 04 OVER
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R1, R0, R2),
                Load(R3, Memory(R1)),
                Binary(Sub, R0, R0, R2),
                Store(R3, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 05 ROT
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R4, R0, R2),
                Load(R3, Memory(R4)),
                Store(R1, Memory(R4)),
                Constant(R2, cell_bytes(2)),
                Binary(Add, R4, R0, R2),
                Load(R1, Memory(R4)),
                Store(R3, Memory(R4)),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 06 -ROT
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(2)),
                Binary(Add, R4, R0, R2),
                Load(R3, Memory(R4)),
                Store(R1, Memory(R4)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R4, R0, R2),
                Load(R1, Memory(R4)),
                Store(R3, Memory(R4)),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 07 TUCK
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R4, R0, R2),
                Load(R3, Memory(R4)),
                Store(R1, Memory(R4)),
                Store(R3, Memory(R0)),
                Binary(Sub, R0, R0, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 08 NIP
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 09 PICK
                Load(R0, Sp),
                Load(R1, Memory(R0)),
            ],
            tests: (0..4).map(|u| {
                (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Eq(Wrapping(u)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Load(R0, Sp),
                            Constant(R2, cell_bytes(u + 1)),
                            Binary(Add, R1, R0, R2),
                            Load(R1, Memory(R1)),
                            Store(R1, Memory(R0)),
                        ],
                        tests: vec![],
                    }),
                )
            }).collect(),
        },
        DecisionTree {
            actions: vec![ // 0a ROLL
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
            ],
            tests: (0..4).map(|u| {
                (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Eq(Wrapping(u)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Constant(R2, cell_bytes(u)),
                            Binary(Add, R4, R0, R2),
                            Load(R3, Memory(R4)),
                        ].into_iter().chain(
                            (0..u).flat_map(|v| {
                                vec![
                                    Constant(R2, cell_bytes(v)),
                                    Binary(Add, R2, R0, R2),
                                    Load(R1, Memory(R2)),
                                    Store(R3, Memory(R2)),
                                    Move(R3, R1),
                                ]
                            })
                        ).chain(
                            vec![
                                Store(R3, Memory(R4)),
                            ]
                        ).collect(),
                        tests: vec![],
                    }),
                )
            }).collect(),
        },
        DecisionTree {
            actions: vec![ // 0b ?DUP
                Load(R0, Sp),
                Load(R1, Memory(R0)),
            ],
            tests: vec![
                (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Constant(R2, cell_bytes(1)),
                            Binary(Sub, R0, R0, R2),
                            Store(R1, Memory(R0)),
                            Store(R0, Sp),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 0c >R
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
                Load(R0, Rp),
                Binary(Sub, R0, R0, R2),
                Store(R1, Memory(R0)),
                Store(R0, Rp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 0d R>
                Load(R0, Rp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Rp),
                Load(R0, Sp),
                Binary(Sub, R0, R0, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 0e R@
                Load(R0, Rp),
                Load(R1, Memory(R0)),
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 0f <
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(Lt, R1, R2, R1),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 10 >
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(Lt, R1, R1, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 11 =
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(Eq, R1, R1, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 12 <>
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(Eq, R1, R1, R2),
                Unary(Not, R1, R1),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 13 0<
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, Wrapping(0)),
                Binary(Lt, R1, R1, R2),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 14 0>
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, Wrapping(0)),
                Binary(Lt, R1, R2, R1),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 15 0=
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, Wrapping(0)),
                Binary(Eq, R1, R2, R1),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 16 0<>
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, Wrapping(0)),
                Binary(Eq, R1, R2, R1),
                Unary(Not, R1, R1),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 17 U<
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(Ult, R1, R2, R1),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 18 U>
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(Ult, R1, R1, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 19 0
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Constant(R2, Wrapping(0)),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1a 1
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Constant(R2, Wrapping(1)),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1b -1
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Constant(R2, -Wrapping(1)),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1c CELL
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Constant(R2, cell_bytes(1)),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1d -CELL
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Constant(R2, -cell_bytes(1)),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1e +
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(Add, R1, R1, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 1f -
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(Sub, R1, R1, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 20 >-<
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(Sub, R1, R2, R1),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 21 1+
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, Wrapping(1)),
                Binary(Add, R1, R1, R2),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 22 1-
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, Wrapping(1)),
                Binary(Sub, R1, R1, R2),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 23 CELL+
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R1, R1, R2),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 24 CELL-
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R1, R1, R2),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 25 *
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(Mul, R1, R1, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
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
                Load(R3, Sp),
                Load(R1, Memory(R3)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R2, R3, R2),
                Load(R0, Memory(R2)),
                Division(UnsignedDivMod, R0, R1, R0, R1),
                Store(R1, Memory(R2)),
                Store(R0, Memory(R3)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2a S/REM
                Load(R3, Sp),
                Load(R1, Memory(R3)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R2, R3, R2),
                Load(R0, Memory(R2)),
                Division(SignedDivMod, R0, R1, R0, R1),
                Store(R1, Memory(R2)),
                Store(R0, Memory(R3)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2b 2/
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, Wrapping(1)),
                Binary(Asr, R1, R1, R2),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2c CELLS
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Mul, R1, R1, R2),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2d ABS
                Load(R0, Sp),
                Load(R1, Memory(R0)),
            ],
            tests: vec![
                (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Lt(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Unary(Negate, R1, R1),
                            Store(R1, Memory(R0)),
                        ],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: R1,
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
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Unary(Negate, R1, R1),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 2f MAX
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
                Load(R2, Memory(R0)),
                Binary(Lt, R3, R2, R1),
            ],
            tests: vec![
                (
                    code::Test {
                        register: R3,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: R3,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Store(R1, Memory(R0)),
                        ],
                        tests: vec![],
                    }),
                )
            ],
        },
        DecisionTree {
            actions: vec![ // 30 MIN
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
                Load(R2, Memory(R0)),
                Binary(Lt, R3, R1, R2),
            ],
            tests: vec![
                (
                    code::Test {
                        register: R3,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: R3,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Store(R1, Memory(R0)),
                        ],
                        tests: vec![],
                    }),
                )
            ],
        },
        DecisionTree {
            actions: vec![ // 31 INVERT
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Unary(Not, R1, R1),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 32 AND
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(And, R1, R1, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 33 OR
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(Or, R1, R1, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 34 XOR
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Binary(Xor, R1, R1, R2),
                Store(R1, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 35 LSHIFT
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![
                (
                    code::Test {
                        register: R2,
                        test_op: TestOp::Ult(CELL_BITS),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Binary(Lsl, R1, R1, R2),
                            Store(R1, Memory(R0)),
                        ],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: R2,
                        test_op: TestOp::Ult(CELL_BITS),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Constant(R1, Wrapping(0)),
                            Store(R1, Memory(R0)),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 36 RSHIFT
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Load(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![
                (
                    code::Test {
                        register: R2,
                        test_op: TestOp::Ult(CELL_BITS),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Binary(Lsr, R1, R1, R2),
                            Store(R1, Memory(R0)),
                        ],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: R2,
                        test_op: TestOp::Ult(CELL_BITS),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Constant(R1, Wrapping(0)),
                            Store(R1, Memory(R0)),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 37 1LSHIFT
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, Wrapping(1)),
                Binary(Lsl, R1, R1, R2),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 38 1RSHIFT
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, Wrapping(1)),
                Binary(Lsr, R1, R1, R2),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 39 @
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Load(R1, Memory(R1)),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3a !
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R2, R0, R2),
                Load(R3, Memory(R2)),
                Store(R3, Memory(R1)),
                Constant(R2, cell_bytes(2)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3b C@
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                LoadNarrow(Width::One, R1, Memory(R1)),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3c C!
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R2, R0, R2),
                Load(R3, Memory(R2)),
                StoreNarrow(Width::One, R3, Memory(R1)),
                Constant(R2, cell_bytes(2)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3d +!
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R2, R0, R2),
                Load(R3, Memory(R2)),
                Load(R4, Memory(R1)),
                Binary(Add, R3, R4, R3),
                Store(R3, Memory(R1)),
                Constant(R2, cell_bytes(2)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3e SP@
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R2, R0, R2),
                Store(R0, Memory(R2)),
                Store(R2, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 3f SP!
                Load(R0, Sp),
                Load(R0, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 40 RP@
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Load(R2, Rp),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 41 RP!
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Store(R1, Rp),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 42 EP@
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Load(R2, Ep),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 43 S0@
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Load(R2, BeetleAddress::S0),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 44 S0!
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Store(R1, BeetleAddress::S0),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 45 R0@
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Load(R2, BeetleAddress::R0),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 46 R0!
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Store(R1, BeetleAddress::R0),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 47 'THROW@
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Load(R2, BeetleAddress::Throw),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 48 'THROW!
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Store(R1, BeetleAddress::Throw),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 49 MEMORY@
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Load(R2, BeetleAddress::Memory0),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 4a 'BAD@
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Load(R2, BeetleAddress::Bad),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 4b -ADDRESS@
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Load(R2, BeetleAddress::NotAddress),
                Store(R2, Memory(R0)),
                Store(R0, Sp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 4c BRANCH
                // Load EP from the cell it points to.
                Load(R0, Ep),
                Load(R0, Memory(R0)),
                Store(R0, Ep), // FIXME: Add check that EP is valid.
                // NEXT. FIXME: Deduplicate
                Load(R0, Ep), // FIXME: Add check that EP is valid.
                Load(R1, Memory(R0)),
                Store(R1, A),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 4d BRANCHI
                // Add A*4 to EP.
                Load(R0, Ep),
                Load(R1, A),
                Constant(R2, cell_bytes(1)),
                Binary(Mul, R1, R1, R2),
                Binary(Add, R0, R0, R1),
                Store(R0, Ep), // FIXME: Add check that EP is valid.
                // NEXT. FIXME: Deduplicate
                Load(R0, Ep), // FIXME: Add check that EP is valid.
                Load(R1, Memory(R0)),
                Store(R1, A),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 4e ?BRANCH
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
            ],
            tests: vec![
                (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            // BRANCH. FIXME: Deduplicate.
                            Load(R0, Ep),
                            Load(R0, Memory(R0)),
                            Store(R0, Ep), // FIXME: Add check that EP is valid.
                            // NEXT. FIXME: Deduplicate
                            Load(R0, Ep), // FIXME: Add check that EP is valid.
                            Load(R1, Memory(R0)),
                            Store(R1, A),
                            Constant(R2, cell_bytes(1)),
                            Binary(Add, R0, R0, R2),
                            Store(R0, Ep),
                        ],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Load(R0, Ep), // FIXME: Add check that EP is valid.
                            Constant(R1, cell_bytes(1)),
                            Binary(Add, R0, R0, R1),
                            Store(R0, Ep),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 4f ?BRANCHI
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
            ],
            tests: vec![
                (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Load(R0, Ep),
                            Load(R1, A),
                            Constant(R2, cell_bytes(1)),
                            Binary(Mul, R1, R1, R2),
                            Binary(Add, R0, R0, R1),
                            Store(R0, Ep), // FIXME: Add check that EP is valid.
                            // NEXT. FIXME: Deduplicate
                            Load(R0, Ep), // FIXME: Add check that EP is valid.
                            Load(R1, Memory(R0)),
                            Store(R1, A),
                            Constant(R2, cell_bytes(1)),
                            Binary(Add, R0, R0, R2),
                            Store(R0, Ep),
                        ],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            // NEXT. FIXME: Deduplicate
                            Load(R0, Ep), // FIXME: Add check that EP is valid.
                            Load(R1, Memory(R0)),
                            Store(R1, A),
                            Constant(R2, cell_bytes(1)),
                            Binary(Add, R0, R0, R2),
                            Store(R0, Ep),
                        ],
                        tests: vec![],
                    }),
                ),
            ],
        },
        DecisionTree {
            actions: vec![ // 50 EXECUTE
                // Push EP onto the return stack.
                Load(R1, Rp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R1, R1, R2),
                Store(R1, Rp),
                Load(R0, Ep),
                Store(R0, Memory(R1)),
                // Put a-addr1 into EP.
                Load(R1, Sp),
                Load(R0, Memory(R1)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R1, R1, R2),
                Store(R1, Sp),
                Store(R0, Ep), // FIXME: Add check that EP is valid.
                // NEXT. FIXME: Deduplicate
                Load(R0, Ep), // FIXME: Add check that EP is valid.
                Load(R1, Memory(R0)),
                Store(R1, A),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 51 @EXECUTE
                // Push EP onto the return stack.
                Load(R1, Rp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R1, R1, R2),
                Store(R1, Rp),
                Load(R0, Ep),
                Store(R0, Memory(R1)),
                // Put the contents of a-addr1 into EP.
                Load(R1, Sp),
                Load(R0, Memory(R1)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R1, R1, R2),
                Store(R1, Sp),
                Load(R0, Memory(R0)),
                Store(R0, Ep), // FIXME: Add check that EP is valid.
                // NEXT. FIXME: Deduplicate
                Load(R0, Ep), // FIXME: Add check that EP is valid.
                Load(R1, Memory(R0)),
                Store(R1, A),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 52 CALL
                // Push EP+4 onto the return stack.
                Load(R1, Rp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R1, R1, R2),
                Store(R1, Rp),
                Load(R0, Ep),
                Binary(Add, R0, R0, R2),
                Store(R0, Memory(R1)),
                // BRANCH. FIXME: Deduplicate
                Load(R0, Ep),
                Load(R0, Memory(R0)),
                Store(R0, Ep), // FIXME: Add check that EP is valid.
                Load(R0, Ep), // FIXME: Add check that EP is valid.
                Load(R1, Memory(R0)),
                Store(R1, A),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 53 CALLI
                // Push EP onto the return stack.
                Load(R1, Rp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R1, R1, R2),
                Store(R1, Rp),
                Load(R0, Ep),
                Store(R0, Memory(R1)),
                // Add A*4 to EP.
                Load(R0, Ep),
                Load(R1, A),
                Constant(R2, cell_bytes(1)),
                Binary(Mul, R1, R1, R2),
                Binary(Add, R0, R0, R1),
                Store(R0, Ep), // FIXME: Add check that EP is valid.
                // NEXT. FIXME: Deduplicate
                Load(R0, Ep), // FIXME: Add check that EP is valid.
                Load(R1, Memory(R0)),
                Store(R1, A),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 54 EXIT
                // Put a-addr into EP.
                Load(R1, Rp),
                Load(R0, Memory(R1)),
                Store(R0, Ep), // FIXME: Add check that EP is valid.
                Constant(R2, cell_bytes(1)),
                Binary(Add, R1, R1, R2),
                Store(R1, Rp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 55 (DO)
                // Pop two items from SP.
                Load(R0, Sp),
                Load(R2, Memory(R0)),
                Constant(R1, cell_bytes(1)),
                Binary(Add, R0, R0, R1),
                Load(R3, Memory(R0)),
                Binary(Add, R0, R0, R1),
                Store(R0, Sp),
                // Push two items to RP.
                Load(R0, Rp),
                Constant(R1, cell_bytes(1)),
                Binary(Sub, R0, R0, R1),
                Store(R3, Memory(R0)),
                Binary(Sub, R0, R0, R1),
                Store(R2, Memory(R0)),
                Store(R0, Rp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 56 (LOOP)
                // Load the index and limit from RP.
                Load(R0, Rp),
                Load(R3, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R2, R0, R2),
                Load(R2, Memory(R2)),
                // Update the index.
                Constant(R1, Wrapping(1)),
                Binary(Add, R3, R3, R1),
                Store(R3, Memory(R0)),
                Binary(Sub, R3, R3, R2),
            ],
            tests: vec![
                (
                    code::Test {
                        register: R3,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            // Discard the loop index and limit.
                            Load(R0, Rp),
                            Constant(R2, cell_bytes(2)),
                            Binary(Add, R0, R0, R2),
                            Store(R0, Rp),
                            // Add 4 to EP.
                            Load(R0, Ep), // FIXME: Add check that EP is valid.
                            Constant(R1, cell_bytes(1)),
                            Binary(Add, R0, R0, R1),
                            Store(R0, Ep),
                        ],
                        tests: vec![],
                    }),
                ), (
                    code::Test {
                        register: R3,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            // BRANCH. FIXME: Deduplicate
                            Load(R0, Ep),
                            Load(R0, Memory(R0)),
                            Store(R0, Ep), // FIXME: Add check that EP is valid.
                            Load(R0, Ep), // FIXME: Add check that EP is valid.
                            Load(R1, Memory(R0)),
                            Store(R1, A),
                            Constant(R2, cell_bytes(1)),
                            Binary(Add, R0, R0, R2),
                            Store(R0, Ep),
                        ],
                        tests: vec![],
                    }),
                )
            ],
        },
        DecisionTree {
            actions: vec![ // 57 (LOOP)I
                // Load the index and limit from RP.
                Load(R0, Rp),
                Load(R3, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R2, R0, R2),
                Load(R2, Memory(R2)),
                // Update the index.
                Constant(R1, Wrapping(1)),
                Binary(Add, R3, R3, R1),
                Store(R3, Memory(R0)),
                Binary(Sub, R3, R3, R2),
            ],
            tests: vec![
                (
                    code::Test {
                        register: R3,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            // Discard the loop index and limit.
                            Load(R0, Rp),
                            Constant(R2, cell_bytes(2)),
                            Binary(Add, R0, R0, R2),
                            Store(R0, Rp),
                        ],
                        tests: vec![]
                    }),
                ), (
                    code::Test {
                        register: R3,
                        test_op: TestOp::Eq(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            // BRANCHI. FIXME: Deduplicate
                            Load(R0, Ep),
                            Load(R1, A),
                            Constant(R2, cell_bytes(1)),
                            Binary(Mul, R1, R1, R2),
                            Binary(Add, R0, R0, R1),
                            Store(R0, Ep), // FIXME: Add check that EP is valid.
                            Load(R0, Ep), // FIXME: Add check that EP is valid.
                            Load(R1, Memory(R0)),
                            Store(R1, A),
                            Constant(R2, cell_bytes(1)),
                            Binary(Add, R0, R0, R2),
                            Store(R0, Ep),
                        ],
                        tests: vec![],
                    }),
                )
            ],
        },
        DecisionTree { // 58 (+LOOP)
            actions: vec![ //
                // Pop the step from SP.
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
                // Load the index and limit from RP.
                Load(R0, Rp),
                Load(R3, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R2, R0, R2),
                Load(R2, Memory(R2)),
                // Update the index.
                Binary(Add, R4, R3, R1),
                Store(R4, Memory(R0)),
                // Compute the differences between old and new indexes and limit.
                Binary(Sub, R3, R3, R2),
                Binary(Sub, R4, R4, R2),
            ],
            tests: vec![
                (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Lt(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Unary(Not, R4, R4),
                            Binary(And, R4, R4, R3),
                        ],
                        tests: vec![
                            (
                                code::Test {
                                    register: R4,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: true,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // Discard the loop index and limit.
                                        Load(R0, Rp),
                                        Constant(R2, cell_bytes(2)),
                                        Binary(Add, R0, R0, R2),
                                        Store(R0, Rp),
                                        // Add 4 to EP.
                                        Load(R0, Ep), // FIXME: Add check that EP is valid.
                                        Constant(R1, cell_bytes(1)),
                                        Binary(Add, R0, R0, R1),
                                        Store(R0, Ep),
                                    ],
                                    tests: vec![],
                                }),
                            ),
                            (
                                code::Test {
                                    register: R4,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: false,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // BRANCH. FIXME: Deduplicate
                                        Load(R0, Ep),
                                        Load(R0, Memory(R0)),
                                        Store(R0, Ep), // FIXME: Add check that EP is valid.
                                        Load(R0, Ep), // FIXME: Add check that EP is valid.
                                        Load(R1, Memory(R0)),
                                        Store(R1, A),
                                        Constant(R2, cell_bytes(1)),
                                        Binary(Add, R0, R0, R2),
                                        Store(R0, Ep),
                                    ],
                                    tests: vec![],
                                }),
                            )
                        ]
                    }),
                ),
                (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Lt(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Unary(Not, R3, R3),
                            Binary(And, R4, R4, R3),
                        ],
                        tests: vec![
                            (
                                code::Test {
                                    register: R4,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: true,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // Discard the loop index and limit.
                                        Load(R0, Rp),
                                        Constant(R2, cell_bytes(2)),
                                        Binary(Add, R0, R0, R2),
                                        Store(R0, Rp),
                                        // Add 4 to EP.
                                        Load(R0, Ep), // FIXME: Add check that EP is valid.
                                        Constant(R1, cell_bytes(1)),
                                        Binary(Add, R0, R0, R1),
                                        Store(R0, Ep),
                                    ],
                                    tests: vec![],
                                }),
                            ),
                            (
                                code::Test {
                                    register: R4,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: false,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // BRANCH. FIXME: Deduplicate
                                        Load(R0, Ep),
                                        Load(R0, Memory(R0)),
                                        Store(R0, Ep), // FIXME: Add check that EP is valid.
                                        Load(R0, Ep), // FIXME: Add check that EP is valid.
                                        Load(R1, Memory(R0)),
                                        Store(R1, A),
                                        Constant(R2, cell_bytes(1)),
                                        Binary(Add, R0, R0, R2),
                                        Store(R0, Ep),
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
                Load(R0, Sp),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Sp),
                // Load the index and limit from RP.
                Load(R0, Rp),
                Load(R3, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R2, R0, R2),
                Load(R2, Memory(R2)),
                // Update the index.
                Binary(Add, R4, R3, R1),
                Store(R4, Memory(R0)),
                // Compute the differences between old and new indexes and limit.
                Binary(Sub, R3, R3, R2),
                Binary(Sub, R4, R4, R2),
            ],
            tests: vec![
                (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Lt(Wrapping(0)),
                        must_be: false,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Unary(Not, R4, R4),
                            Binary(And, R4, R4, R3),
                        ],
                        tests: vec![
                            (
                                code::Test {
                                    register: R4,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: true,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // Discard the loop index and limit.
                                        Load(R0, Rp),
                                        Constant(R2, cell_bytes(2)),
                                        Binary(Add, R0, R0, R2),
                                        Store(R0, Rp),
                                    ],
                                    tests: vec![],
                                }),
                            ),
                            (
                                code::Test {
                                    register: R4,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: false,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // BRANCHI. FIXME: Deduplicate
                                        Load(R0, Ep),
                                        Load(R1, A),
                                        Constant(R2, cell_bytes(1)),
                                        Binary(Mul, R1, R1, R2),
                                        Binary(Add, R0, R0, R1),
                                        Store(R0, Ep), // FIXME: Add check that EP is valid.
                                        Load(R0, Ep), // FIXME: Add check that EP is valid.
                                        Load(R1, Memory(R0)),
                                        Store(R1, A),
                                        Constant(R2, cell_bytes(1)),
                                        Binary(Add, R0, R0, R2),
                                        Store(R0, Ep),
                                    ],
                                    tests: vec![],
                                }),
                            )
                        ]
                    }),
                ),
                (
                    code::Test {
                        register: R1,
                        test_op: TestOp::Lt(Wrapping(0)),
                        must_be: true,
                    },
                    Box::new(DecisionTree {
                        actions: vec![
                            Unary(Not, R3, R3),
                            Binary(And, R4, R4, R3),
                        ],
                        tests: vec![
                            (
                                code::Test {
                                    register: R4,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: true,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // Discard the loop index and limit.
                                        Load(R0, Rp),
                                        Constant(R2, cell_bytes(2)),
                                        Binary(Add, R0, R0, R2),
                                        Store(R0, Rp),
                                    ],
                                    tests: vec![],
                                }),
                            ),
                            (
                                code::Test {
                                    register: R4,
                                    test_op: TestOp::Lt(Wrapping(0)),
                                    must_be: false,
                                },
                                Box::new(DecisionTree {
                                    actions: vec![
                                        // BRANCHI. FIXME: Deduplicate
                                        Load(R0, Ep),
                                        Load(R1, A),
                                        Constant(R2, cell_bytes(1)),
                                        Binary(Mul, R1, R1, R2),
                                        Binary(Add, R0, R0, R1),
                                        Store(R0, Ep), // FIXME: Add check that EP is valid.
                                        Load(R0, Ep), // FIXME: Add check that EP is valid.
                                        Load(R1, Memory(R0)),
                                        Store(R1, A),
                                        Constant(R2, cell_bytes(1)),
                                        Binary(Add, R0, R0, R2),
                                        Store(R0, Ep),
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
                Load(R0, Rp),
                Constant(R1, cell_bytes(2)),
                Binary(Add, R0, R0, R1),
                Store(R0, Rp),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 5b J
                // Push the third item of RP to SP.
                Load(R0, Rp),
                Constant(R1, cell_bytes(2)),
                Binary(Add, R0, R0, R1),
                Load(R2, Memory(R0)),
                Load(R0, Sp),
                Constant(R1, cell_bytes(1)),
                Binary(Sub, R0, R0, R1),
                Store(R0, Sp),
                Store(R2, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 5c (LITERAL)
                // Load R1 from cell pointed to by EP, and add 4 to EP.
                Load(R0, Ep),
                Load(R1, Memory(R0)),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Ep), // FIXME: Add check that EP is valid.
                // Push R1 to the stack.
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Store(R0, Sp),
                Store(R1, Memory(R0)),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 5d (LITERAL)I
                // Push A to the stack.
                Load(R0, Sp),
                Constant(R2, cell_bytes(1)),
                Binary(Sub, R0, R0, R2),
                Store(R0, Sp),
                Load(R1, A),
                Store(R1, Memory(R0)),
                // NEXT. FIXME: Deduplicate
                Load(R0, Ep), // FIXME: Add check that EP is valid.
                Load(R1, Memory(R0)),
                Store(R1, A),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Ep),
            ],
            tests: vec![],
        },
        DecisionTree {
            actions: vec![ // 5e THROW
                // Set 'BAD to EP
                Load(R0, Ep),
                Store(R0, BeetleAddress::Bad),
                // Load EP from 'THROW
                Load(R0, BeetleAddress::Throw),
                Load(R0, Memory(R0)),
                Store(R0, Ep), // FIXME: Add check that EP is valid.
                // NEXT. FIXME: Deduplicate
                Load(R0, Ep), // FIXME: Add check that EP is valid.
                Load(R1, Memory(R0)),
                Store(R1, A),
                Constant(R2, cell_bytes(1)),
                Binary(Add, R0, R0, R2),
                Store(R0, Ep),
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