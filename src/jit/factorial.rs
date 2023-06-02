use super::code::*;
use Action::*;
use BinaryOp::*;
use Precision::*;
use Width::*;
use super::target::{Target, Word};
use super::{EntryId, Jit};

/// `GLOBAL` points to this.
#[repr(C)]
pub struct Registers {n: u64, result: u64}

/// A [`Register`] that holds `1`.
pub const ONE: Register = REGISTERS[1];
/// A [`Register`] that holds the loop counter.
pub const N: Register = REGISTERS[2];
/// A [`Register`] that holds the accumulator.
pub const RESULT: Register = REGISTERS[3];

/// An example that can be used as a test fixture.
#[derive(Debug)]
pub struct Factorial<T: Target> {
    /// The state of the JIT compiler.
    pub jit: Jit<T>,
    /// The entry point.
    pub start: EntryId,
}

const START: i64 = 0;
const LOOP: i64 = 1;
const HALT: i64 = 2;

impl<T: Target> Factorial<T> {
    pub fn new(target: T) -> Factorial<T> {
        let mut jit = Jit::new(target);
        let marshal = Marshal {
            prologue: Box::new([
                // Restore `N`.
                Load(N, Address {base: GLOBAL.into(), offset: 0, width: Eight}),
                // Restore `RESULT`.
                Load(RESULT, Address {base: GLOBAL.into(), offset: 8, width: Eight}),
                // Restore `ONE`.
                Constant(P32, ONE, 1),
            ]),
            epilogue: Box::new([
                // No need to save `ONE`, but we must use it. Dummy op.
                Send(GLOBAL, GLOBAL.into(), ONE.into()),
                // Save `N`.
                Store(GLOBAL, N.into(), Address {base: GLOBAL.into(), offset: 0, width: Eight}),
                // Save `RESULT`.
                Store(GLOBAL, RESULT.into(), Address {base: GLOBAL.into(), offset: 8, width: Eight}),
            ]),
        };
        let start = jit.new_entry(&marshal, START);
        let loop_ = jit.new_entry(&marshal, LOOP);
        let halt = jit.new_entry(&marshal, HALT);
        jit.define(start, EBB {
            actions: Box::new([
                Constant(P32, RESULT, 1),
            ]),
            ending: Ending::Leaf(loop_),
        });
        jit.define(loop_, EBB {
            actions: Box::new([]),
            ending: Ending::Switch(N.into(), Switch::if_(
                EBB {
                    actions: Box::new([
                        Binary(Mul, P32, RESULT, RESULT.into(), N.into()),
                        Binary(Sub, P32, N, N.into(), ONE.into()),
                    ]),
                    ending: Ending::Leaf(loop_),
                },
                EBB {
                    actions: Box::new([]),
                    ending: Ending::Leaf(halt),
                },
            )),
        });
        Factorial {jit, start}
    }

    pub fn run(&mut self, n: u64) -> u64 {
        let mut regs = Registers {n, result: 0};
        let exit_value = unsafe {self.jit.run(self.start, &mut regs)};
        assert_eq!(exit_value, Word {s: HALT});
        regs.result
    }
}
