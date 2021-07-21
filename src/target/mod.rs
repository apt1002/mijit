use super::{buffer, code};

mod pool;
pub use pool::{Counter, Word, Pool};

mod label;
pub use label::{Patch, Label};

mod traits;
pub use traits::{Lower, ExecuteFn, Execute, Target};

pub mod x86_64;
pub mod aarch64;

/**
 * The [`Register`] which holds the state index on entry and exit from Mijit.
 * This is guaranteed to be [`REGISTERS`][[`0`]].
 */
// TODO: Somehow hide the state index from this module, and delete this.
pub const STATE_INDEX: code::Register = code::REGISTERS[0];

/** A [`Target`] that generates code which can be executed. */
pub fn native() -> impl Target {
    #[cfg(target_arch="x86_64")]
    return x86_64::Target;
    #[cfg(target_arch="aarch64")]
    return aarch64::Target;
    #[allow(unreachable_code)] {
        panic!("Unknown target");
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    use code::{Register, REGISTERS, Slot, Global, Precision, UnaryOp, BinaryOp, Width, AliasMask, Action};
    use Precision::*;
    use UnaryOp::*;
    use BinaryOp::*;
    use Width::*;
    use Action::*;

    /** A test harness for a `T::Lowerer`. */
    pub struct VM<T: Target> {
        pub lowerer: T::Lowerer,
        pub entry: Label,
    }

    impl<T: Target> VM<T> {
        /** Constructs a `T::Lowerer` and passes it to `compile()`. */
        pub fn new(target: T, num_globals: usize, compile: impl FnOnce(&mut T::Lowerer)) -> Self {
            let mut lowerer = target.lowerer(Pool::new(num_globals));
            let entry = lowerer.here();
            lowerer.prologue();
            compile(&mut lowerer);
            lowerer.epilogue();
            Self {lowerer, entry}
        }

        /**
         * Calls the compiled code after setting the `Global`s to the specified
         * values, and checks that the return value is `expected_result`.
         */
        pub fn run(mut self, globals: &[Word], expected_result: Word) -> Self {
            assert_eq!(globals.len(), self.lowerer.pool().num_globals());
            for (i, &global) in globals.iter().enumerate() {
                self.lowerer.pool_mut()[Global(i)] = global;
            }
            let (lowerer, observed_result) = self.lowerer.execute(&self.entry, |f, pool| {
                f(pool.as_mut().as_mut_ptr(), Word {u: 0})
            }).expect("Couldn't change permissions");
            self.lowerer = lowerer;
            if observed_result != expected_result {
                println!("globals = {:?}", globals);
                println!("observed = {:?}", observed_result);
                println!("expected = {:?}", expected_result);
                panic!("observed != expected");
            }
            self
        }
    }

    pub const R0: Register = REGISTERS[0];
    pub const R1: Register = REGISTERS[1];
    pub const R2: Register = REGISTERS[2];

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

    /** Constructs a [`VM`], then calls it passing example values. */
    pub fn test_unary(compile: impl FnOnce(&mut dyn Lower), expected: impl Fn(u64) -> u64) {
        let mut vm = VM::new(native(), 1, |lo| compile(lo));
        for x in TEST_VALUES {
            vm = vm.run(&[Word {u: x}], Word {u: expected(x)});
        }
    }

    /** Constructs a [`VM`], then calls it passing example pairs of values. */
    pub fn test_binary(compile: impl FnOnce(&mut dyn Lower), expected: impl Fn(u64, u64) -> u64) {
        let mut vm = VM::new(native(), 2, |lo| compile(lo));
        for x in TEST_VALUES {
            for y in TEST_VALUES {
                vm = vm.run(&[Word {u: x}, Word {u: y}], Word {u: expected(x, y)});
            }
        }
    }

    /** Constructs a [`VM`], then calls it passing a pointer. */
    pub fn test_mem(compile: impl FnOnce(&mut dyn Lower), expected: impl Fn(u64, &mut [u64; 1]) -> u64) {
        let mut vm = VM::new(native(), 1, |lo| compile(lo));
        for x in TEST_VALUES {
            let mut memory = [x];
            vm = vm.run(&[Word {mp: memory.as_mut_ptr() as *mut ()}], Word {u: expected(x, &mut memory)});
        }        
    }

    // Move, Constant, Push, Pop, DropMany.

    #[test]
    fn push_pop() {
        test_unary(
            |lo| {
                assert_eq!(*lo.slots_used(), 0);
                lo.action(Push(None, Some(Global(0).into())));
                assert_eq!(*lo.slots_used(), 2);
                lo.action(Pop(None, Some(R0.into())));
                assert_eq!(*lo.slots_used(), 0);
            },
            |x| x,
        );
        test_unary(
            |lo| {
                assert_eq!(*lo.slots_used(), 0);
                lo.action(Push(Some(Global(0).into()), None));
                assert_eq!(*lo.slots_used(), 2);
                lo.action(Pop(Some(R0.into()), None));
                assert_eq!(*lo.slots_used(), 0);
            },
            |x| x,
        );
    }

    #[test]
    fn drop_many() {
        test_unary(
            |lo| {
                assert_eq!(*lo.slots_used(), 0);
                lo.action(Push(None, None));
                assert_eq!(*lo.slots_used(), 2);
                lo.action(Push(None, Some(Global(0).into())));
                assert_eq!(*lo.slots_used(), 4);
                lo.action(Push(None, None));
                assert_eq!(*lo.slots_used(), 6);
                lo.action(Push(None, None));
                assert_eq!(*lo.slots_used(), 8);
                lo.action(DropMany(2));
                assert_eq!(*lo.slots_used(), 4);
                lo.action(Pop(None, Some(R0.into())));
                assert_eq!(*lo.slots_used(), 2);
                lo.action(DropMany(1));
                assert_eq!(*lo.slots_used(), 0);
            },
            |x| x,
        );
    }

    #[test]
    fn move_() {
        for variable in [R0.into(), Slot(0).into(), Global(0).into()] {
            test_unary(
                |lo| {
                    lo.action(Push(None, None));
                    lo.action(Constant(P64, R0, 42));
                    lo.action(Move(Slot(0).into(), R0.into()));
                    lo.action(Move(variable, Global(0).into()));
                    lo.action(Move(R0.into(), variable));
                    lo.action(Pop(None, None));
                },
                |x| x,
            );
        }
    }

    #[test]
    fn constant() {
        for x in TEST_VALUES {
            let vm = VM::new(native(), 0, |lo| {
                lo.action(Constant(P32, R0, x as i64));
            });
            vm.run(&[], Word {u: x as u32 as u64});
            let vm = VM::new(native(), 0, |lo| {
                lo.action(Constant(P64, R0, x as i64));
            });
            vm.run(&[], Word {u: x});
        }
    }

    // UnaryOps.

    #[test]
    fn abs() {
        test_unary(
            |lo| { lo.action(Unary(Abs, P32, R0, Global(0).into())); },
            |x| (if x as i32 == i32::MIN { x as i32 } else { (x as i32).abs() }) as u32 as u64,
        );
        test_unary(
            |lo| { lo.action(Unary(Abs, P64, R0, Global(0).into())); },
            |x| (if x as i64 == i64::MIN {x as i64 } else { (x as i64).abs() }) as u64,
        );
    }

    #[test]
    fn negate() {
        test_unary(
            |lo| { lo.action(Unary(Negate, P32, R0, Global(0).into())); },
            |x| (if x as i32 == i32::MIN { x as i32 } else { -(x as i32) }) as u32 as u64,
        );
        test_unary(
            |lo| { lo.action(Unary(Negate, P64, R0, Global(0).into())); },
            |x| (if x as i64 == i64::MIN {x as i64 } else { -(x as i64) }) as u64,
        );
    }

    #[test]
    fn not() {
        test_unary(
            |lo| { lo.action(Unary(Not, P32, R0, Global(0).into())); },
            |x| !(x as u32) as u64,
        );
        test_unary(
            |lo| { lo.action(Unary(Not, P64, R0, Global(0).into())); },
            |x| !x,
        );
    }

    // BinaryOps.

    #[test]
    fn add() {
        test_binary(
            |lo| { lo.action(Binary(Add, P32, R0, Global(0).into(), Global(1).into())); },
            |x, y| (x as u32).wrapping_add(y as u32) as u64,
        );
        test_binary(
            |lo| { lo.action(Binary(Add, P64, R0, Global(0).into(), Global(1).into())); },
            |x, y| x.wrapping_add(y),
        );
    }

    #[test]
    fn sub() {
        test_binary(
            |lo| { lo.action(Binary(Sub, P32, R0, Global(0).into(), Global(1).into())); },
            |x, y| (x as u32).wrapping_sub(y as u32) as u64,
        );
        test_binary(
            |lo| { lo.action(Binary(Sub, P64, R0, Global(0).into(), Global(1).into())); },
            |x, y| x.wrapping_sub(y),
        );
    }

    #[test]
    fn mul() {
        test_binary(
            |lo| { lo.action(Binary(Mul, P32, R0, Global(0).into(), Global(1).into())); },
            |x, y| (x as u32).wrapping_mul(y as u32) as u64,
        );
        test_binary(
            |lo| { lo.action(Binary(Mul, P64, R0, Global(0).into(), Global(1).into())); },
            |x, y| x.wrapping_mul(y),
        );
    }

    /**
     * Representative shift amounts.
     * Shifts < 0 or >= word size are undefined.
     */
    const SHIFTS: [usize; 5] = [0, 1, 21, 31, 63];

    #[test]
    fn lsl() {
        for shift in SHIFTS {
            if shift < 32 {
                test_unary(
                    |lo| {
                        lo.action(Constant(P64, R0, shift as i64));
                        lo.action(Binary(Lsl, P32, R0, Global(0).into(), R0.into()));
                    },
                    |x| ((x as u32) << shift) as u64,
                );
            }
            test_unary(
                |lo| {
                    lo.action(Constant(P64, R0, shift as i64));
                    lo.action(Binary(Lsl, P64, R0, Global(0).into(), R0.into()));
                },
                |x| x << shift,
            );
        }
    }

    #[test]
    fn lsr() {
        for shift in SHIFTS {
            if shift < 32 {
                test_unary(
                    |lo| {
                        lo.action(Constant(P64, R0, shift as i64));
                        lo.action(Binary(Lsr, P32, R0, Global(0).into(), R0.into()));
                    },
                    |x| ((x as u32) >> shift) as u64,
                );
            }
            test_unary(
                |lo| {
                    lo.action(Constant(P64, R0, shift as i64));
                    lo.action(Binary(Lsr, P64, R0, Global(0).into(), R0.into()));
                },
                |x| x >> shift,
            );
        }
    }

    #[test]
    fn asr() {
        for shift in SHIFTS {
            if shift < 32 {
                test_unary(
                    |lo| {
                        lo.action(Constant(P64, R0, shift as i64));
                        lo.action(Binary(Asr, P32, R0, Global(0).into(), R0.into()));
                    },
                    |x| ((x as i32) >> shift) as u32 as u64,
                );
            }
            test_unary(
                |lo| {
                    lo.action(Constant(P64, R0, shift as i64));
                    lo.action(Binary(Asr, P64, R0, Global(0).into(), R0.into()));
                },
                |x| ((x as i64) >> shift) as u64,
            );
        }
    }

    #[test]
    fn and() {
        test_binary(
            |lo| { lo.action(Binary(And, P32, R0, Global(0).into(), Global(1).into())); },
            |x, y| ((x as u32) & (y as u32)) as u64,
        );
        test_binary(
            |lo| { lo.action(Binary(And, P64, R0, Global(0).into(), Global(1).into())); },
            |x, y| x & y,
        );
    }

    #[test]
    fn or() {
        test_binary(
            |lo| { lo.action(Binary(Or, P32, R0, Global(0).into(), Global(1).into())); },
            |x, y| ((x as u32) | (y as u32)) as u64,
        );
        test_binary(
            |lo| { lo.action(Binary(Or, P64, R0, Global(0).into(), Global(1).into())); },
            |x, y| x | y,
        );
    }

    #[test]
    fn xor() {
        test_binary(
            |lo| { lo.action(Binary(Xor, P32, R0, Global(0).into(), Global(1).into())); },
            |x, y| ((x as u32) ^ (y as u32)) as u64,
        );
        test_binary(
            |lo| { lo.action(Binary(Xor, P64, R0, Global(0).into(), Global(1).into())); },
            |x, y| x ^ y,
        );
    }

    #[test]
    fn lt() {
        test_binary(
            |lo| { lo.action(Binary(Lt, P32, R0, Global(0).into(), Global(1).into())); },
            |x, y| (if (x as i32) < (y as i32) { !0 as u32 } else { 0 }) as u64,
        );
        test_binary(
            |lo| { lo.action(Binary(Lt, P64, R0, Global(0).into(), Global(1).into())); },
            |x, y| if (x as i64) < (y as i64) { !0 } else { 0 },
        );
    }

    #[test]
    fn ult() {
        test_binary(
            |lo| { lo.action(Binary(Ult, P32, R0, Global(0).into(), Global(1).into())); },
            |x, y| (if (x as u32) < (y as u32) { !0 as u32 } else { 0 }) as u64,
        );
        test_binary(
            |lo| { lo.action(Binary(Ult, P64, R0, Global(0).into(), Global(1).into())); },
            |x, y| if x < y { !0 } else { 0 },
        );
    }

    #[test]
    fn eq() {
        test_binary(
            |lo| { lo.action(Binary(Eq, P32, R0, Global(0).into(), Global(1).into())); },
            |x, y| (if (x as u32) == (y as u32) { !0 as u32 } else { 0 }) as u64,
        );
        test_binary(
            |lo| { lo.action(Binary(Eq, P64, R0, Global(0).into(), Global(1).into())); },
            |x, y| if x == y { !0 } else { 0 },
        );
    }

    #[test]
    fn max() {
        test_binary(
            |lo| { lo.action(Binary(Max, P32, R0, Global(0).into(), Global(1).into())); },
            |x, y| std::cmp::max(x as i32, y as i32) as u32 as u64,
        );
        test_binary(
            |lo| { lo.action(Binary(Max, P64, R0, Global(0).into(), Global(1).into())); },
            |x, y| std::cmp::max(x as i64, y as i64) as u64,
        );
    }

    #[test]
    fn min() {
        test_binary(
            |lo| { lo.action(Binary(Min, P32, R0, Global(0).into(), Global(1).into())); },
            |x, y| std::cmp::min(x as i32, y as i32) as u32 as u64,
        );
        test_binary(
            |lo| { lo.action(Binary(Min, P64, R0, Global(0).into(), Global(1).into())); },
            |x, y| std::cmp::min(x as i64, y as i64) as u64,
        );
    }

    // Load and Store.

    #[test]
    fn load() {
        test_mem(
            |lo| { lo.action(Load(R0, (Global(0).into(), One), AliasMask(1))); },
            |x, _| x as u8 as u64,
        );
        test_mem(
            |lo| { lo.action(Load(R0, (Global(0).into(), Two), AliasMask(1))); },
            |x, _| x as u16 as u64,
        );
        test_mem(
            |lo| { lo.action(Load(R0, (Global(0).into(), Four), AliasMask(1))); },
            |x, _| x as u32 as u64,
        );
        test_mem(
            |lo| { lo.action(Load(R0, (Global(0).into(), Eight), AliasMask(1))); },
            |x, _| x,
        );
    }

    #[test]
    fn store() {
        const DATA: u64 = 0x5555555555555555;
        // Check returned address.
        test_mem(
            |lo| {
                lo.action(Constant(P64, R1, DATA as i64));
                lo.action(Store(R0, R1.into(), (Global(0).into(), Eight), AliasMask(1)));
            },
            |_, p| p.as_mut_ptr() as u64,
        );
        // Check returned address gets stored.
        test_mem(
            |lo| {
                lo.action(Constant(P64, R0, DATA as i64));
                lo.action(Store(R0, R0.into(), (Global(0).into(), Eight), AliasMask(1)));
                lo.action(Load(R0, (Global(0).into(), Eight), AliasMask(1)));
            },
            |_, p| p.as_mut_ptr() as u64,
        );
        // Check all `Width`s.
        test_mem(
            |lo| {
                lo.action(Constant(P64, R0, DATA as i64));
                lo.action(Store(R1, R0.into(), (Global(0).into(), One), AliasMask(1)));
                lo.action(Load(R0, (Global(0).into(), Eight), AliasMask(1)));
            },
            |x, _| {
                (x ^ DATA) as u8 as u64 ^ x
            },
        );
        test_mem(
            |lo| {
                lo.action(Constant(P64, R0, DATA as i64));
                lo.action(Store(R1, R0.into(), (Global(0).into(), Two), AliasMask(1)));
                lo.action(Load(R0, (Global(0).into(), Eight), AliasMask(1)));
            },
            |x, _| (x ^ DATA) as u16 as u64 ^ x,
        );
        test_mem(
            |lo| {
                lo.action(Constant(P64, R0, DATA as i64));
                lo.action(Store(R1, R0.into(), (Global(0).into(), Four), AliasMask(1)));
                lo.action(Load(R0, (Global(0).into(), Eight), AliasMask(1)));
            },
            |x, _| (x ^ DATA) as u32 as u64 ^ x,
        );
        test_mem(
            |lo| {
                lo.action(Constant(P64, R0, DATA as i64));
                lo.action(Store(R1, R0.into(), (Global(0).into(), Eight), AliasMask(1)));
                lo.action(Load(R0, (Global(0).into(), Eight), AliasMask(1)));
            },
            |_, _| DATA,
        );
    }

    // TestOps.

    #[test]
    fn eq_test() {
        for y in TEST_VALUES {
            let mut vm = VM::new(native(), 1, |lo| {
                let mut else_ = Label::new(None);
                let mut endif = Label::new(None);
                lo.test_eq((Global(0).into(), y), &mut else_);
                lo.action(Constant(P64, R0, !0));
                lo.jump(&mut endif);
                lo.define(&mut else_);
                lo.action(Constant(P64, R0, 0));
                lo.define(&mut endif);
            });
            for x in TEST_VALUES {
                vm = vm.run(&[Word {u: x}], Word {u: if x == y { !0 } else { 0 }});
            }
        }
    }

    // Test extremes.

    #[test]
    fn long_jump() {
        // Choose an order in which to visit a large number of blocks.
        const SIZE: usize = 0x10000;
        let permutation = crate::util::permutation(SIZE);
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
        let vm = VM::new(native(), 0, |lo| {
            let mut labels: Vec<Label> = permutation.iter().map(|_| Label::new(None)).collect();
            let mut exit = Label::new(None);
            lo.action(Constant(P64, R0, 0));
            lo.jump(&mut labels[permutation[0]]);
            for i in 0..permutation.len() {
                lo.define(&mut labels[i]);
                // Rotate `R0` right by 21 places.
                lo.action(Constant(P64, R2, 21));
                lo.action(Binary(Lsr, P64, R1, R0.into(), R2.into()));
                lo.action(Constant(P64, R2, 64 - 21));
                lo.action(Binary(Lsl, P64, R0, R0.into(), R2.into()));
                lo.action(Binary(Or, P64, R0, R0.into(), R1.into()));
                // Add `constants[i]` to `R0`.
                lo.action(Constant(P64, R2, constants[i] as i64));
                lo.action(Binary(Add, P64, R0, R0.into(), R2.into()));
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
        vm.run(&[], Word {u: expected});
    }
}
