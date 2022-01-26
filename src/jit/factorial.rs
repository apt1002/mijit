use super::code::*;
use Action::*;
use BinaryOp::*;
use Precision::*;
use super::target::{Target, Word};
use super::{EntryId, Jit2};

const R0: Register = REGISTERS[0];

pub mod reg {
    use super::{Global, Variable};
    pub const N: Variable = Variable::Global(Global(0));
    pub const RESULT: Variable = Variable::Global(Global(1));
}

/** An example that can be used as a test fixture. */
pub struct Factorial<T: Target> {
    /** The state of the JIT compiler. */
    pub jit: Jit2<T>,
    /** The entry point. */
    pub start: EntryId,
}

const START: i64 = 0;
const LOOP: i64 = 1;
const HALT: i64 = 2;

impl<T: Target> Factorial<T> {
    pub fn new(target: T) -> Factorial<T> {
        let mut jit = Jit2::new(target, 2);
        let marshal = Marshal {prologue: Box::new([]), epilogue: Box::new([])};
        let start = jit.new_entry(&marshal, START);
        let loop_ = jit.new_entry(&marshal, LOOP);
        let halt = jit.new_entry(&marshal, HALT);
        jit.define(start, &EBB {
            actions: vec![
                Constant(P32, R0, 1),
                Move(reg::RESULT, R0.into()),
            ],
            ending: Ending::Leaf(loop_),
        });
        jit.define(loop_, &EBB {
            actions: vec![],
            ending: Ending::Switch(Switch::if_(
                reg::N,
                EBB {
                    actions: vec![
                        Binary(Mul, P32, R0, reg::RESULT, reg::N),
                        Move(reg::RESULT, R0.into()),
                        Constant(P32, R0, 1),
                        Binary(Sub, P32, R0, reg::N, R0.into()),
                        Move(reg::N, R0.into()),
                    ],
                    ending: Ending::Leaf(loop_),
                },
                EBB {
                    actions: vec![],
                    ending: Ending::Leaf(halt),
                },
            )),
        });
        Factorial {jit, start}
    }

    pub fn run(mut self, n: u64) -> std::io::Result<(Self, u64)> {
        let n_global = Global::try_from(reg::N).unwrap();
        let result_global = Global::try_from(reg::RESULT).unwrap();
        *self.jit.global_mut(n_global) = Word {u: n};
        let (jit, exit_value) = unsafe {self.jit.run(self.start)}?;
        assert_eq!(exit_value, Word {s: HALT});
        self.jit = jit;
        let result = *self.jit.global_mut(result_global);
        Ok((self, unsafe {result.u}))
    }
}
