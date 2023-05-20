use super::{buffer, code};

mod word;
pub use word::{Word};

mod label;
pub use label::{Patch, Label};

mod traits;
pub use traits::{Lower, ExecuteFn, Execute, Target};

pub mod x86_64;
pub mod aarch64;

/// The [`code::Register`] which holds the exit code on exit from Mijit.
/// This is guaranteed to be [`code::REGISTERS`]`[[0]]`.
pub const RESULT: code::Register = code::REGISTERS[0];

#[cfg(target_arch="x86_64")]
pub type Native = x86_64::Target;
#[cfg(target_arch="aarch64")]
pub type Native = aarch64::Target;

/// Returns the current [`Target`]. Equivalent to [`Default::default()`].
pub fn native() -> Native {
    Default::default()
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    use code::{Register, REGISTERS, GLOBAL, Slot, Precision, UnaryOp, BinaryOp, Width, Address, Action};
    use Precision::*;
    use UnaryOp::*;
    use BinaryOp::*;
    use Width::*;
    use Action::*;

    /// A test harness for a `Native::Lowerer`.
    pub struct VM {
        pub lowerer: <Native as Target>::Lowerer,
        pub entry: Label,
    }

    impl VM {
        /// Constructs a `Native::Lowerer` and passes it to `compile()`.
        /// The compiled code gets arguments in `inputs` and returns a result
        /// in `RESULT`.
        pub fn new(inputs: &[Register], compile: impl FnOnce(&mut dyn Lower)) -> Self {
            let mut lowerer = native().lowerer();
            let entry = lowerer.here();
            lowerer.prologue();
            for (i, &r) in inputs.iter().enumerate() {
                // Load `GLOBAL[i]` into `r`.
                assert_ne!(r, GLOBAL);
                lowerer.action(Load(r, Address {base: GLOBAL.into(), offset: i as i32 * 8, width: Eight}));
            }
            compile(&mut lowerer);
            lowerer.epilogue();
            Self {lowerer, entry}
        }

        /// Calls the compiled code after setting the `inputs` to the specified
        /// values, and checks that the return value is `expected_result`.
        pub unsafe fn run(mut self, inputs: &mut [Word], expected_result: Word) -> Self {
            let global = inputs.as_mut_ptr() as *mut ();
            let observed_result = self.lowerer.execute(&self.entry, |f| {
                f(global)
            });
            if observed_result != expected_result {
                println!("inputs = {:?}", inputs);
                println!("observed = {:?}", observed_result);
                println!("expected = {:?}", expected_result);
                panic!("observed != expected");
            }
            self
        }
    }

    pub const R1: Register = REGISTERS[1];
    pub const R2: Register = REGISTERS[2];
    pub const R3: Register = REGISTERS[3];

    pub const TEST_VALUES: [u64; 22] = [
        0x0000000000000000,
        0x0000000000000001,
        0x0000000011111111,
        0x000000007FFFFFFF,
        0x0000000080000000,
        0x00000000EEEEEEEE,
        0x00000000FFFFFFFE,
        0x00000000FFFFFFFF,
        0x0123456789ABCDEF,
        0x1111111111111111,
        0x7FFFFFFFFFFFFFFF,
        0x8000000000000000,
        0xEEEEEEEEEEEEEEEE,
        0xFEDCBA9876543210,
        0xFFFFFFFF00000000,
        0xFFFFFFFF00000001,
        0xFFFFFFFF11111111,
        0xFFFFFFFF7FFFFFFF,
        0xFFFFFFFF80000000,
        0xFFFFFFFFEEEEEEEE,
        0xFFFFFFFFFFFFFFFE,
        0xFFFFFFFFFFFFFFFF,
    ];

    /// Constructs a [`VM`], then calls it passing example values.
    pub unsafe fn test_unary(compile: impl FnOnce(&mut dyn Lower), expected: impl Fn(u64) -> u64) {
        let mut vm = VM::new(&[R1], |lo| compile(lo));
        for x in TEST_VALUES {
            vm = vm.run(
                &mut [Word {u: x}],
                Word {u: expected(x)},
            );
        }
    }

    /// Constructs a [`VM`], then calls it passing example pairs of values.
    pub unsafe fn test_binary(compile: impl FnOnce(&mut dyn Lower), expected: impl Fn(u64, u64) -> u64) {
        let mut vm = VM::new(&[R1, R2], |lo| compile(lo));
        for x in TEST_VALUES {
            for y in TEST_VALUES {
                vm = vm.run(
                    &mut [Word {u: x}, Word {u: y}],
                    Word {u: expected(x, y)},
                );
            }
        }
    }

    /// Constructs a [`VM`], then calls it passing a pointer.
    pub unsafe fn test_mem(compile: impl FnOnce(&mut dyn Lower), expected: impl Fn(u64, &mut [u64; 2]) -> u64) {
        let mut vm = VM::new(&[R1], |lo| compile(lo));
        for x in TEST_VALUES {
            let mut memory = [x, !x];
            vm = vm.run(
                &mut [Word {mp: memory.as_mut_ptr() as *mut ()}],
                Word {u: expected(x, &mut memory)},
            );
        }        
    }

    /// Test that the results of arithmetic operations do not depend on which
    /// registers are used to compute them.
    ///  - compile - Takes (lo, dest, src1, src2).
    pub unsafe fn test_clobber(
        compile: impl Fn(&mut dyn Lower, Register, Register, Register),
    ) {
        for dest in [R1, R2] {
            let mut vm = VM::new(&[R1, R2], |lo| {
                compile(lo, R3, R1, R2);
                compile(lo, dest, R1, R2);
                lo.action(Binary(Xor, P64, RESULT, dest.into(), R3.into()));
            });
            for x in TEST_VALUES {
                for y in [1, 11, 31] {
                    vm = vm.run(
                        &mut [Word {u: x}, Word {u: y}],
                        Word {u: 0},
                    );
                }
            }
        }
    }

    // Move, Constant, Push, Drop.

    #[test]
    fn push() {
        unsafe {test_unary(
            |lo| {
                assert_eq!(*lo.slots_used_mut(), 0);
                lo.action(Push(None, Some(R1.into())));
                assert_eq!(*lo.slots_used_mut(), 2);
                lo.action(Move(RESULT.into(), Slot(0).into()));
                lo.action(Drop(1));
                assert_eq!(*lo.slots_used_mut(), 0);
            },
            |x| x,
        )};
        unsafe {test_unary(
            |lo| {
                assert_eq!(*lo.slots_used_mut(), 0);
                lo.action(Push(Some(R1.into()), None));
                assert_eq!(*lo.slots_used_mut(), 2);
                lo.action(Move(RESULT.into(), Slot(1).into()));
                lo.action(Drop(1));
                assert_eq!(*lo.slots_used_mut(), 0);
            },
            |x| x,
        )};
    }

    #[test]
    fn drop() {
        unsafe {test_unary(
            |lo| {
                assert_eq!(*lo.slots_used_mut(), 0);
                lo.action(Push(None, None));
                assert_eq!(*lo.slots_used_mut(), 2);
                lo.action(Push(None, Some(R1.into())));
                assert_eq!(*lo.slots_used_mut(), 4);
                lo.action(Push(None, None));
                assert_eq!(*lo.slots_used_mut(), 6);
                lo.action(Push(None, None));
                assert_eq!(*lo.slots_used_mut(), 8);
                lo.action(Drop(2));
                assert_eq!(*lo.slots_used_mut(), 4);
                lo.action(Move(RESULT.into(), Slot(2).into()));
                assert_eq!(*lo.slots_used_mut(), 4);
                lo.action(Drop(2));
                assert_eq!(*lo.slots_used_mut(), 0);
            },
            |x| x,
        )};
    }

    #[test]
    fn move_() {
        for variable in [R1.into(), Slot(0).into()] {
            unsafe {test_unary(
                |lo| {
                    lo.action(Push(None, None));
                    lo.action(Constant(P64, RESULT, 42));
                    lo.action(Move(Slot(0).into(), RESULT.into()));
                    lo.action(Move(variable, R1.into()));
                    lo.action(Move(RESULT.into(), variable));
                    lo.action(Drop(1));
                },
                |x| x,
            )};
        }
    }

    #[test]
    fn constant() {
        for x in TEST_VALUES {
            let vm = VM::new(&[], |lo| {
                lo.action(Constant(P32, RESULT, x as i64));
            });
            unsafe {vm.run(&mut [], Word {u: x as u32 as u64})};
            let vm = VM::new(&[], |lo| {
                lo.action(Constant(P64, RESULT, x as i64));
            });
            unsafe {vm.run(&mut [], Word {u: x})};
        }
    }

    // UnaryOps.

    #[test]
    fn abs() {
        unsafe {test_unary(
            |lo| { lo.action(Unary(Abs, P32, RESULT, R1.into())); },
            |x| (if x as i32 == i32::MIN { x as i32 } else { (x as i32).abs() }) as u32 as u64,
        )};
        unsafe {test_unary(
            |lo| { lo.action(Unary(Abs, P64, RESULT, R1.into())); },
            |x| (if x as i64 == i64::MIN { x as i64 } else { (x as i64).abs() }) as u64,
        )};
    }

    #[test]
    fn negate() {
        unsafe {test_unary(
            |lo| { lo.action(Unary(Negate, P32, RESULT, R1.into())); },
            |x| (if x as i32 == i32::MIN { x as i32 } else { -(x as i32) }) as u32 as u64,
        )};
        unsafe {test_unary(
            |lo| { lo.action(Unary(Negate, P64, RESULT, R1.into())); },
            |x| (if x as i64 == i64::MIN {x as i64 } else { -(x as i64) }) as u64,
        )};
    }

    #[test]
    fn not() {
        unsafe {test_unary(
            |lo| { lo.action(Unary(Not, P32, RESULT, R1.into())); },
            |x| !(x as u32) as u64,
        )};
        unsafe {test_unary(
            |lo| { lo.action(Unary(Not, P64, RESULT, R1.into())); },
            |x| !x,
        )};
    }

    #[test]
    fn clobber_unary() {
        for op in [Abs, Negate, Not] {
            for prec in [P32, P64] {
                unsafe {test_clobber(|lo, dest, src1, _| {
                    lo.action(Unary(op, prec, dest, src1.into()));
                })};
            }
        }
    }

    // BinaryOps.

    #[test]
    fn add() {
        unsafe {test_binary(
            |lo| { lo.action(Binary(Add, P32, RESULT, R1.into(), R2.into())); },
            |x, y| (x as u32).wrapping_add(y as u32) as u64,
        )};
        unsafe {test_binary(
            |lo| { lo.action(Binary(Add, P64, RESULT, R1.into(), R2.into())); },
            |x, y| x.wrapping_add(y),
        )};
    }

    #[test]
    fn sub() {
        unsafe {test_binary(
            |lo| { lo.action(Binary(Sub, P32, RESULT, R1.into(), R2.into())); },
            |x, y| (x as u32).wrapping_sub(y as u32) as u64,
        )};
        unsafe {test_binary(
            |lo| { lo.action(Binary(Sub, P64, RESULT, R1.into(), R2.into())); },
            |x, y| x.wrapping_sub(y),
        )};
    }

    #[test]
    fn mul() {
        unsafe {test_binary(
            |lo| { lo.action(Binary(Mul, P32, RESULT, R1.into(), R2.into())); },
            |x, y| (x as u32).wrapping_mul(y as u32) as u64,
        )};
        unsafe {test_binary(
            |lo| { lo.action(Binary(Mul, P64, RESULT, R1.into(), R2.into())); },
            |x, y| x.wrapping_mul(y),
        )};
    }

    #[test]
    fn udiv() {
        // P32.
        let mut vm = VM::new(&[R1, R2], |lo| {
            lo.action(Binary(UDiv, P32, RESULT, R1.into(), R2.into()));
        });
        for x in TEST_VALUES {
            let x2 = x as u32;
            for y in TEST_VALUES {
                let y2 = y as u32;
                if y2 == 0 {
                    // Undefined behaviour.
                } else {
                    let expected = x2 / y2;
                    vm = unsafe {vm.run(
                        &mut [Word {u: x}, Word {u: y}],
                        Word {u: expected as u64},
                    )};
                }
            }
        }
        // P64.
        let mut vm = VM::new(&[R1, R2], |lo| {
            lo.action(Binary(UDiv, P64, RESULT, R1.into(), R2.into()));
        });
        for x in TEST_VALUES {
            let x2 = x as u64;
            for y in TEST_VALUES {
                let y2 = y as u64;
                if y == 0 {
                    // Undefined behaviour.
                } else {
                    let expected = x2 / y2;
                    vm = unsafe {vm.run(
                        &mut [Word {u: x}, Word {u: y}],
                        Word {u: expected},
                    )};
                }
            }
        }
    }

    #[test]
    fn sdiv() {
        // P32.
        let mut vm = VM::new(&[R1, R2], |lo| {
            lo.action(Binary(SDiv, P32, RESULT, R1.into(), R2.into()));
        });
        for x in TEST_VALUES {
            let x2 = x as i32;
            for y in TEST_VALUES {
                let y2 = y as i32;
                if y2 == 0 {
                    // Undefined behaviour.
                } else if x2 == -0x80000000 && y2 == -1 {
                    // Undefined behaviour.
                } else {
                    let expected = x2 / y2;
                    vm = unsafe {vm.run(
                        &mut [Word {u: x}, Word {u: y}],
                        Word {u: expected as u32 as u64},
                    )};
                }
            }
        }
        // P64.
        let mut vm = VM::new(&[R1, R2], |lo| {
            lo.action(Binary(SDiv, P64, RESULT, R1.into(), R2.into()));
        });
        for x in TEST_VALUES {
            let x2 = x as i64;
            for y in TEST_VALUES {
                let y2 = y as i64;
                if y2 == 0 {
                    // Undefined behaviour.
                } else if x2 == -0x8000000000000000 && y2 == -1 {
                    // Undefined behaviour.
                } else {
                    let expected = x2 / y2;
                    vm = unsafe {
                        vm.run(&mut [Word {u: x}, Word {u: y}],
                        Word {u: expected as u64},
                    )};
                }
            }
        }
    }

    /// Representative shift amounts.
    /// Shifts < 0 or >= word size are undefined.
    const SHIFTS: [usize; 5] = [0, 1, 21, 31, 63];

    #[test]
    fn lsl() {
        for shift in SHIFTS {
            if shift < 32 {
                unsafe {test_unary(
                    |lo| {
                        lo.action(Constant(P64, RESULT, shift as i64));
                        lo.action(Binary(Lsl, P32, RESULT, R1.into(), RESULT.into()));
                    },
                    |x| ((x as u32) << shift) as u64,
                )};
            }
            unsafe {test_unary(
                |lo| {
                    lo.action(Constant(P64, RESULT, shift as i64));
                    lo.action(Binary(Lsl, P64, RESULT, R1.into(), RESULT.into()));
                },
                |x| x << shift,
            )};
        }
    }

    #[test]
    fn lsr() {
        for shift in SHIFTS {
            if shift < 32 {
                unsafe {test_unary(
                    |lo| {
                        lo.action(Constant(P64, RESULT, shift as i64));
                        lo.action(Binary(Lsr, P32, RESULT, R1.into(), RESULT.into()));
                    },
                    |x| ((x as u32) >> shift) as u64,
                )};
            }
            unsafe {test_unary(
                |lo| {
                    lo.action(Constant(P64, RESULT, shift as i64));
                    lo.action(Binary(Lsr, P64, RESULT, R1.into(), RESULT.into()));
                },
                |x| x >> shift,
            )};
        }
    }

    #[test]
    fn asr() {
        for shift in SHIFTS {
            if shift < 32 {
                unsafe {test_unary(
                    |lo| {
                        lo.action(Constant(P64, RESULT, shift as i64));
                        lo.action(Binary(Asr, P32, RESULT, R1.into(), RESULT.into()));
                    },
                    |x| ((x as i32) >> shift) as u32 as u64,
                )};
            }
            unsafe {test_unary(
                |lo| {
                    lo.action(Constant(P64, RESULT, shift as i64));
                    lo.action(Binary(Asr, P64, RESULT, R1.into(), RESULT.into()));
                },
                |x| ((x as i64) >> shift) as u64,
            )};
        }
    }

    #[test]
    fn and() {
        unsafe {test_binary(
            |lo| { lo.action(Binary(And, P32, RESULT, R1.into(), R2.into())); },
            |x, y| ((x as u32) & (y as u32)) as u64,
        )};
        unsafe {test_binary(
            |lo| { lo.action(Binary(And, P64, RESULT, R1.into(), R2.into())); },
            |x, y| x & y,
        )};
    }

    #[test]
    fn or() {
        unsafe {test_binary(
            |lo| { lo.action(Binary(Or, P32, RESULT, R1.into(), R2.into())); },
            |x, y| ((x as u32) | (y as u32)) as u64,
        )};
        unsafe {test_binary(
            |lo| { lo.action(Binary(Or, P64, RESULT, R1.into(), R2.into())); },
            |x, y| x | y,
        )};
    }

    #[test]
    fn xor() {
        unsafe {test_binary(
            |lo| { lo.action(Binary(Xor, P32, RESULT, R1.into(), R2.into())); },
            |x, y| ((x as u32) ^ (y as u32)) as u64,
        )};
        unsafe {test_binary(
            |lo| { lo.action(Binary(Xor, P64, RESULT, R1.into(), R2.into())); },
            |x, y| x ^ y,
        )};
    }

    #[test]
    fn lt() {
        unsafe {test_binary(
            |lo| { lo.action(Binary(Lt, P32, RESULT, R1.into(), R2.into())); },
            |x, y| (if (x as i32) < (y as i32) { !0 as u32 } else { 0 }) as u64,
        )};
        unsafe {test_binary(
            |lo| { lo.action(Binary(Lt, P64, RESULT, R1.into(), R2.into())); },
            |x, y| if (x as i64) < (y as i64) { !0 } else { 0 },
        )};
    }

    #[test]
    fn ult() {
        unsafe {test_binary(
            |lo| { lo.action(Binary(Ult, P32, RESULT, R1.into(), R2.into())); },
            |x, y| (if (x as u32) < (y as u32) { !0 as u32 } else { 0 }) as u64,
        )};
        unsafe {test_binary(
            |lo| { lo.action(Binary(Ult, P64, RESULT, R1.into(), R2.into())); },
            |x, y| if x < y { !0 } else { 0 },
        )};
    }

    #[test]
    fn eq() {
        unsafe {test_binary(
            |lo| { lo.action(Binary(Eq, P32, RESULT, R1.into(), R2.into())); },
            |x, y| (if (x as u32) == (y as u32) { !0 as u32 } else { 0 }) as u64,
        )};
        unsafe {test_binary(
            |lo| { lo.action(Binary(Eq, P64, RESULT, R1.into(), R2.into())); },
            |x, y| if x == y { !0 } else { 0 },
        )};
    }

    #[test]
    fn max() {
        unsafe {test_binary(
            |lo| { lo.action(Binary(Max, P32, RESULT, R1.into(), R2.into())); },
            |x, y| std::cmp::max(x as i32, y as i32) as u32 as u64,
        )};
        unsafe {test_binary(
            |lo| { lo.action(Binary(Max, P64, RESULT, R1.into(), R2.into())); },
            |x, y| std::cmp::max(x as i64, y as i64) as u64,
        )};
    }

    #[test]
    fn min() {
        unsafe {test_binary(
            |lo| { lo.action(Binary(Min, P32, RESULT, R1.into(), R2.into())); },
            |x, y| std::cmp::min(x as i32, y as i32) as u32 as u64,
        )};
        unsafe {test_binary(
            |lo| { lo.action(Binary(Min, P64, RESULT, R1.into(), R2.into())); },
            |x, y| std::cmp::min(x as i64, y as i64) as u64,
        )};
    }

    #[test]
    fn clobber_binary() {
        for op in [
            Add, Sub, Mul, UDiv, SDiv,
            Lsl, Lsr, Asr,
            And, Or, Xor,
            Lt, Ult, Eq,
            Max, Min,
        ] {
            for prec in [P32, P64] {
                unsafe {test_clobber(|lo, dest, src1, src2| {
                    lo.action(Binary(op, prec, dest, src1.into(), src2.into()));
                })};
            }
        }
    }

    // Load and Store.

    #[test]
    fn load() {
        for (offset, mask) in [(0, 0), (8, !0)] {
            unsafe {test_mem(
                |lo| { lo.action(Load(RESULT, Address {base: R1.into(), offset, width: One})); },
                |x, _| (x ^ mask) as u8 as u64,
            )};
            unsafe {test_mem(
                |lo| { lo.action(Load(RESULT, Address {base: R1.into(), offset, width: Two})); },
                |x, _| (x ^ mask) as u16 as u64,
            )};
            unsafe {test_mem(
                |lo| { lo.action(Load(RESULT, Address {base: R1.into(), offset, width: Four})); },
                |x, _| (x ^ mask) as u32 as u64,
            )};
            unsafe {test_mem(
                |lo| { lo.action(Load(RESULT, Address {base: R1.into(), offset, width: Eight})); },
                |x, _| (x ^ mask),
            )};
        }
    }

    #[test]
    fn store() {
        const DATA: u64 = 0x5555555555555555;
        for (offset, mask) in [(0, 0), (8, !0)] {
            // Check returned address.
            unsafe {test_mem(
                |lo| {
                    lo.action(Constant(P64, R2, DATA as i64));
                    lo.action(Store(RESULT, R2.into(), Address {base: R1.into(), offset, width: Eight}));
                },
                |_, p| p.as_mut_ptr() as u64,
            )};
            // Check value stored at the returned address.
            unsafe {test_mem(
                |lo| {
                    lo.action(Constant(P64, R2, DATA as i64));
                    lo.action(Store(RESULT, R2.into(), Address {base: R1.into(), offset, width: Eight}));
                    lo.action(Load(RESULT, Address {base: R1.into(), offset, width: Eight}));
                },
                |_, _p| DATA,
            )};
            // Check value stored at the returned address when `dest == src`.
            unsafe {test_mem(
                |lo| {
                    lo.action(Constant(P64, RESULT, DATA as i64));
                    lo.action(Store(RESULT, RESULT.into(), Address {base: R1.into(), offset, width: Eight}));
                    lo.action(Load(RESULT, Address {base: R1.into(), offset, width: Eight}));
                },
                |_, _p| DATA,
            )};
            // Check value stored at the returned address when `dest == addr`.
            unsafe {test_mem(
                |lo| {
                    lo.action(Constant(P64, R2, DATA as i64));
                    lo.action(Move(RESULT.into(), R1.into()));
                    lo.action(Store(RESULT, R2.into(), Address {base: RESULT.into(), offset, width: Eight}));
                    lo.action(Load(RESULT, Address {base: R1.into(), offset, width: Eight}));
                },
                |_, _p| DATA,
            )};
            // Check all `Width`s.
            unsafe {test_mem(
                |lo| {
                    lo.action(Constant(P64, RESULT, DATA as i64));
                    lo.action(Store(R1, RESULT.into(), Address {base: R1.into(), offset, width: One}));
                    lo.action(Load(RESULT, Address {base: R1.into(), offset, width: Eight}));
                },
                |x, _| {
                    let y = x ^ mask;
                    (y ^ DATA) as u8 as u64 ^ y
                },
            )};
            unsafe {test_mem(
                |lo| {
                    lo.action(Constant(P64, RESULT, DATA as i64));
                    lo.action(Store(R1, RESULT.into(), Address {base: R1.into(), offset, width: Two}));
                    lo.action(Load(RESULT, Address {base: R1.into(), offset, width: Eight}));
                },
                |x, _| {
                    let y = x ^ mask;
                    (y ^ DATA) as u16 as u64 ^ y
                },
            )};
            unsafe {test_mem(
                |lo| {
                    lo.action(Constant(P64, RESULT, DATA as i64));
                    lo.action(Store(R1, RESULT.into(), Address {base: R1.into(), offset, width: Four}));
                    lo.action(Load(RESULT, Address {base: R1.into(), offset, width: Eight}));
                },
                |x, _| {
                    let y = x ^ mask;
                    (y ^ DATA) as u32 as u64 ^ y
                },
            )};
            unsafe {test_mem(
                |lo| {
                    lo.action(Constant(P64, RESULT, DATA as i64));
                    lo.action(Store(R1, RESULT.into(), Address {base: R1.into(), offset, width: Eight}));
                    lo.action(Load(RESULT, Address {base: R1.into(), offset, width: Eight}));
                },
                |_, _| DATA,
            )};
        }
    }

    // TestOps.

    const TRUE: u64 = !0;
    const FALSE: u64 = 0;

    #[test]
    fn if_eq() {
        for y in TEST_VALUES {
            let mut vm = VM::new(&[R1], |lo| {
                let mut else_ = Label::new(None);
                let mut endif = Label::new(None);
                lo.if_eq((R1.into(), y), &mut else_);
                lo.action(Constant(P64, RESULT, FALSE as i64));
                lo.jump(&mut endif);
                lo.define(&mut else_);
                lo.action(Constant(P64, RESULT, TRUE as i64));
                lo.define(&mut endif);
            });
            for x in TEST_VALUES {
                vm = unsafe {vm.run(
                    &mut [Word {u: x}],
                    Word {u: if x == y { TRUE } else { FALSE }},
                )};
            }
        }
    }

    #[test]
    fn if_ne() {
        for y in TEST_VALUES {
            let mut vm = VM::new(&[R1], |lo| {
                let mut else_ = Label::new(None);
                let mut endif = Label::new(None);
                lo.if_ne((R1.into(), y), &mut else_);
                lo.action(Constant(P64, RESULT, FALSE as i64));
                lo.jump(&mut endif);
                lo.define(&mut else_);
                lo.action(Constant(P64, RESULT, TRUE as i64));
                lo.define(&mut endif);
            });
            for x in TEST_VALUES {
                vm = unsafe {vm.run(
                    &mut [Word {u: x}],
                    Word {u: if x != y { TRUE } else { FALSE }},
                )};
            }
        }
    }

    // Test extremes.

    /// Generate a pseudo-random permutation of size `size`.
    fn permutation(size: usize) -> Vec<usize> {
        let mut nats: Vec<usize> = (0..size).collect();
        let mut seed: u32 = 1;
        (0..size).map(|_| {
            seed = seed.wrapping_mul(314159265).wrapping_add(271828183);
            let index = ((nats.len() as u64) * (seed as u64)) >> 32;
            nats.swap_remove(index as usize)
        }).collect()
    }

    #[test]
    fn long_jump() {
        // Choose an order in which to visit a large number of blocks.
        const SIZE: usize = 0x10000;
        let permutation = permutation(SIZE);
        // Work out which block each block jumps to.
        let mut nexts: Vec<Option<usize>> = vec![None; SIZE];
        let mut prev = permutation[0];
        for &p in &permutation[1..SIZE] {
            nexts[prev] = Some(p);
            prev = p;
        }
        // Choose a pseudo-random constant per block.
        let constants: Vec<u64> = permutation.iter().map(|&p|
            (p as u64).wrapping_mul(39564853453457569)
        ).collect();
        // Compile all the blocks.
        let vm = VM::new(&[], |lo| {
            let mut labels: Vec<Label> = permutation.iter().map(|_| Label::new(None)).collect();
            let mut exit = Label::new(None);
            lo.action(Constant(P64, RESULT, 0));
            lo.jump(&mut labels[permutation[0]]);
            for i in 0..permutation.len() {
                lo.define(&mut labels[i]);
                // Rotate `RESULT` right by 21 places.
                lo.action(Constant(P64, R2, 21));
                lo.action(Binary(Lsr, P64, R1, RESULT.into(), R2.into()));
                lo.action(Constant(P64, R2, 64 - 21));
                lo.action(Binary(Lsl, P64, RESULT, RESULT.into(), R2.into()));
                lo.action(Binary(Or, P64, RESULT, RESULT.into(), R1.into()));
                // Add `constants[i]` to `RESULT`.
                lo.action(Constant(P64, R2, constants[i] as i64));
                lo.action(Binary(Add, P64, RESULT, RESULT.into(), R2.into()));
                // Jump to next block.
                if let Some(next) = nexts[i] {
                    lo.jump(&mut labels[next]);
                } else {
                    lo.jump(&mut exit);
                }
            }
            lo.define(&mut exit);
        });
        // Check against the expected result.
        let mut expected: u64 = 0;
        for p in permutation {
            expected = crate::util::rotate_right(expected, 21).wrapping_add(constants[p]);
        }
        unsafe {vm.run(&mut [], Word {u: expected})};
    }
}
