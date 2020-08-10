use std::{mem};
use indexmap::{IndexSet};

use super::{Buffer, code, x86_64};
use code::{Action, TestOp, Machine, Precision};
use x86_64::*;
use Register::*;
use Precision::*;
use BinaryOp::*;
use ShiftOp::*;
use Condition;

/**
 * Represents the convention by which code passes values to a label. The
 * concept is similar to a calling convention, but it's for a jump, not a call.
 *
 * This is a place-holder. Possible future uses:
 *  - Register and spill-slot allocation, including dead values.
 *  - Knowledge about values, e.g. minimum and maximum possible value, and
 *    which bits are known to be set or clear.
 *  - Knowledge about possible common sub-expressions, e.g. knowing that some
 *    value is the difference of two other values.
 *  - Knowledge about the cache state, e.g. that some value is the value of
 *    some memory location, and whether it needs to be stored.
 */
pub struct Convention {
    /** The Register whose value will be tested next. */
    pub test_register: code::R,
}

pub struct History<M: code::Machine> {
    /** The test which must pass in order to execute `fetch`. */
    pub test: TestOp,
    /** The code for the unique "fetch" transition to this History. */
    pub fetch: Vec<Action<M::Memory, M::Global>>,
    /** The interface from `fetch` to `retire`. */
    pub convention: Convention,
    /** The code for the unique "retire" transition from this History. */
    pub retire: Vec<Action<M::Memory, M::Global>>,
    /** All jump instructions whose target is `retire`. */
    pub retire_labels: Vec<Label>,
}

/**
 * The type of the generated code.
 *  - current_index - the index of the current M::State in `states`.
 * Returns:
 *  - new_index - updated `current_index`.
 */
type RunFn = extern "C" fn(
    /* pool */ *mut u64,
    /* current_index */  usize,
) -> /* new_index */ usize;

//-----------------------------------------------------------------------------

struct JitAssembler<'a, M: Machine> {
    pub a: Assembler<'a>,
    pub machine: &'a M,
    pub globals: &'a IndexSet<M::Global>,
}

impl <'a, M: Machine> JitAssembler<'a, M> {
    /** Returns the offset of `global` in the persistent data. */
    fn global_offset(&self, global: &M::Global) -> i32 {
        let index = self.globals.get_index_of(global).expect("Unknown global");
        (index * 8) as i32
    }

    /**
     * Assemble code that branches to `false_label` if `test_op` is false.
     */
    fn lower_test_op(
        &mut self,
        test_op: code::TestOp,
        prec: Precision,
        false_label: &mut Label,
    ) {
        match test_op {
            TestOp::Bits(discriminant, mask, value) => {
                self.a.const_(prec, RC, mask as i64);
                self.a.op(And, prec, RC, discriminant);
                self.a.const_op(Cmp, prec, RC, value as i32);
                self.a.jump_if(Condition::Z, false, false_label);
            },
            TestOp::Lt(discriminant, value) => {
                self.a.const_op(Cmp, prec, discriminant, value as i32);
                self.a.jump_if(Condition::L, false, false_label);
            },
            TestOp::Ge(discriminant, value) => {
                self.a.const_op(Cmp, prec, discriminant, value as i32);
                self.a.jump_if(Condition::GE, false, false_label);
            },
            TestOp::Ult(discriminant, value) => {
                self.a.const_op(Cmp, prec, discriminant, value as i32);
                self.a.jump_if(Condition::B, false, false_label);
            },
            TestOp::Uge(discriminant, value) => {
                self.a.const_op(Cmp, prec, discriminant, value as i32);
                self.a.jump_if(Condition::AE, false, false_label);
            },
            TestOp::Eq(discriminant, value) => {
                self.a.const_op(Cmp, prec, discriminant, value as i32);
                self.a.jump_if(Condition::Z, false, false_label);
            },
            TestOp::Ne(discriminant, value) => {
                self.a.const_op(Cmp, prec, discriminant, value as i32);
                self.a.jump_if(Condition::NZ, false, false_label);
            },
            TestOp::Always => {},
        };
    }
    
    /**
     * Assemble code to perform the given `unary_op`.
     */
    fn lower_unary_op(
        &mut self,
        unary_op: code::UnaryOp,
        prec: Precision,
        dest: code::R,
        src: code::R,
    ) {
        match unary_op {
            code::UnaryOp::Abs => {
                self.a.move_(prec, RC, src);
                self.a.const_(prec, dest, 0);
                self.a.op(Sub, prec, dest, RC);
                self.a.move_if(Condition::L, true, prec, dest, RC);
            },
            code::UnaryOp::Negate => {
                self.a.move_(prec, RC, src);
                self.a.const_(prec, dest, 0);
                self.a.op(Sub, prec, dest, RC);
            },
            code::UnaryOp::Not => {
                self.a.move_(prec, dest, src);
                self.a.const_op(Xor, prec, dest, -1);
            },
        };
    }

    /**
     * Assemble code to perform the given `binary_op`.
     */
    fn lower_binary_op(
        &mut self,
        binary_op: code::BinaryOp,
        prec: Precision,
        dest: code::R,
        src1: code::R,
        src2: code::R,
    ) {
        match binary_op {
            code::BinaryOp::Add => {
                self.a.move_(prec, dest, src1);
                self.a.op(Add, prec, dest, src2);
            },
            code::BinaryOp::Sub => {
                self.a.move_(prec, dest, src1);
                self.a.op(Sub, prec, dest, src2);
            },
            code::BinaryOp::Mul => {
                self.a.move_(prec, dest, src1);
                self.a.mul(prec, dest, src2);
            },
            // TODO: Define what happens when you shift too far.
            code::BinaryOp::Lsl => {
                self.a.move_(prec, dest, src1);
                self.a.move_(P32, RC, src2);
                self.a.shift(Shl, prec, dest);
            },
            code::BinaryOp::Lsr => {
                self.a.move_(prec, dest, src1);
                self.a.move_(P32, RC, src2);
                self.a.shift(Shr, prec, dest);
            },
            code::BinaryOp::Asr => {
                self.a.move_(prec, dest, src1);
                self.a.move_(P32, RC, src2);
                self.a.shift(Sar, prec, dest);
            },
            code::BinaryOp::And => {
                self.a.move_(prec, dest, src1);
                self.a.op(And, prec, dest, src2);
            },
            code::BinaryOp::Or => {
                self.a.move_(prec, dest, src1);
                self.a.op(Or, prec, dest, src2);
            },
            code::BinaryOp::Xor => {
                self.a.move_(prec, dest, src1);
                self.a.op(Xor, prec, dest, src2);
            },
            code::BinaryOp::Lt => {
                self.a.const_(prec, RC, -1);
                self.a.const_(prec, dest, 0);
                self.a.op(Cmp, prec, src1, src2);
                self.a.move_if(Condition::L, true, prec, dest, RC);
            },
            code::BinaryOp::Ult => {
                self.a.const_(prec, RC, -1);
                self.a.const_(prec, dest, 0);
                self.a.op(Cmp, prec, src1, src2);
                self.a.move_if(Condition::B, true, prec, dest, RC);
            },
            code::BinaryOp::Eq => {
                self.a.const_(prec, RC, -1);
                self.a.const_(prec, dest, 0);
                self.a.op(Cmp, prec, src1, src2);
                self.a.move_if(Condition::Z, true, prec, dest, RC);
            },
            code::BinaryOp::Max => {
                self.a.op(Cmp, prec, src1, src2);
                self.a.move_(prec, dest, src2);
                self.a.move_if(Condition::G, true, prec, dest, src1);
            },
            code::BinaryOp::Min => {
                self.a.op(Cmp, prec, src1, src2);
                self.a.move_(prec, dest, src2);
                self.a.move_if(Condition::L, true, prec, dest, src1);
            },
        };
    }

    fn lower_memory_location(mloc: code::MemoryLocation<M::Memory>) -> (code::R, x86_64::Width) {
        use code::MemoryLocation::*;
        match mloc {
            One(addr, _m) => (addr, x86_64::Width::U8),
            Two(addr, _m) => (addr, x86_64::Width::U16),
            Four(addr, _m) => (addr, x86_64::Width::U32),
            Eight(addr, _m) => (addr, x86_64::Width::U64),
        }
    }

    /**
     * Assemble code to perform the given `action`.
     */
    fn lower_action(
        &mut self,
        action: Action<M::Memory, M::Global>,
    ) {
        match action {
            Action::Constant(prec, dest, value) => {
                self.a.const_(prec, dest, value);
            },
            Action::Move(prec, dest, src) => {
                self.a.move_(prec, dest, src);
            },
            Action::Unary(op, prec, dest, src) => {
                self.lower_unary_op(op, prec, dest, src);
            },
            Action::Binary(op, prec, dest, src1, src2) => {
                self.lower_binary_op(op, prec, dest, src1, src2);
            },
            Action::Division(_op, _prec, _, _, _, _) => {
                panic!("FIXME: Don't know how to assemble div");
            },
            Action::LoadGlobal(dest, global) => {
                let offset = self.global_offset(&global);
                self.a.load(P64, dest, (R8, offset));
            },
            Action::StoreGlobal(src, global) => {
                let offset = self.global_offset(&global);
                self.a.store(P64, (R8, offset), src);
            },
            Action::Load(prec, dest, mloc) => {
                let (addr, width) = Self::lower_memory_location(mloc);
                self.a.load_narrow(prec, width, dest, (addr, 0));
            },
            Action::Store(src, mloc) => {
                let (addr, width) = Self::lower_memory_location(mloc);
                self.a.store_narrow(width, (addr, 0), src);
            },
            Action::Push(src) => {
                self.a.push(src);
            },
            Action::Pop(dest) => {
                self.a.pop(dest);
            },
            Action::Debug => {
                self.a.debug();
            },
        };
    }
}

//-----------------------------------------------------------------------------

/**
 * The state of the JIT compiler. This includes the memory allocated for the
 * compiled code, the [`Machine`] we're compiling, and all house-keeping data.
 */
pub struct Jit<M: Machine> {
    machine: M,
    /** Numbering of all M::States. */
    states: IndexSet<M::State>,
    /** Numbering of all M::Globals. */
    globals: IndexSet<M::Global>,
    /**
     * The locations of the compiled code for all retire transitions,
     * and of all instructions that jump to them.
     */
    fetch_labels: Vec<Label>,
    /**
     * The locations of the compiled code for all retire transitions,
     * and of all instructions that jump to them.
     */
    retire_labels: Vec<Label>,
    /** The mmapped memory buffer containing the compiled code. */
    buffer: Buffer,
    /** The number of bytes of `buffer` already occupied. */
    used: usize,
    /** The pool of mutable storage locations. */
    pool: Vec<u64>,
}

impl<M: Machine> Jit<M> {
    pub fn new(machine: M, code_size: usize) -> Self {
        // Enumerate the reachable states in FIFO order.
        // Simultaneously enumerate all globals.
        let mut states: IndexSet<M::State> = machine.initial_states().into_iter().collect();
        let mut globals: IndexSet<M::Global> = IndexSet::new();
        let mut done = 0;
        while let Some(state) = states.get_index(done) {
            for (_test_op, actions, new_state) in machine.get_code(state.clone()) {
                let _ = states.insert(new_state);
                for action in actions {
                    if let Some(global) = match action {
                        Action::LoadGlobal(_, global) => Some(global),
                        Action::StoreGlobal(_, global) => Some(global),
                        _ => None,
                    } {
                        globals.insert(global.clone());
                    }
                }
            }
            done += 1;
        }

        // Assemble the function prologue.
        let mut fetch_labels: Vec<Label> = (0..states.len()).map(|_| Label::new(None)).collect();
        let mut retire_labels: Vec<Label> = (0..states.len()).map(|_| Label::new(None)).collect();
        let mut buffer = Buffer::new(code_size).expect("couldn't allocate memory");
        let mut a = Assembler::new(&mut buffer);
        for &r in &CALLEE_SAVES {
            a.push(r);
        }
        a.move_(P64, R8, RDI);
        for (index, &_) in states.iter().enumerate() {
            a.const_op(Cmp, P32, RSI, index as i32);
            a.jump_if(Condition::Z, true, &mut fetch_labels[index]);
        }
        a.const_(P32, RA, -1);

        // Assemble the function epilogue.
        let mut epilogue = Label::new(None);
        a.define(&mut epilogue);
        for &r in CALLEE_SAVES.iter().rev() {
            a.pop(r);
        }
        a.ret();

        // Construct the root labels.
        for (index, _) in states.iter().enumerate() {
            a.define(&mut fetch_labels[index]);
            a.const_jump(&mut retire_labels[index]);
            a.define(&mut retire_labels[index]);
            a.const_(P32, RA, index as i64);
            a.const_jump(&mut epilogue);
        }

        // Construct the Jit.
        let used = a.get_pos();
        let pool = vec![0; globals.len()];
        let mut jit = Jit {machine, states, globals, fetch_labels, retire_labels, buffer, used, pool};

        // Construct the root Histories.
        let all_states: Vec<_> = jit.states.iter().cloned().collect();
        for old_state in all_states {
            for ((test_op, prec), actions, new_state) in jit.machine.get_code(old_state.clone()) {
                let old_index = jit.states.get_index_of(&old_state).unwrap();
                let new_index = jit.states.get_index_of(&new_state).unwrap();
                jit.insert_history(old_index, test_op, prec, actions, new_index);
            }
        }

        jit
    }

    pub fn used(&self) -> usize {
        self.used
    }

    pub fn states(&self) -> &IndexSet<M::State> {
        &self.states
    }

    pub fn globals(&self) -> &IndexSet<M::Global> {
        &self.globals
    }

    pub fn global(&mut self, global: &M::Global) -> &mut u64 {
        let index = self.globals.get_index_of(global).expect("Unknown global");
        &mut self.pool[index]
    }

    /**
     * Construct a History.
     *  - old_index - the index of the History that will become the right
     *    parent of the new History. TODO: Rename.
     *  - new_index - the index of the History that will become the left
     *    parent of the new History. TODO: Rename.
     *  - test_op - the boolean test which distinguishes the new History from
     *    its right parent. The new History will be reached only if its right
     *    parent is reached and `test_op` passes.
     *  - actions - the code that must be executed before retiring to the left
     *    parent of the new History. This code will be optimized and divided
     *    between the fetch and retire transitions.
     *
     * TODO: Actually construct and return a History. At the moment we just
     * assemble the code.
     */
    fn insert_history(
        &mut self,
        old_index: usize,
        test_op: code::TestOp,
        prec: Precision,
        actions: Vec<Action<M::Memory, M::Global>>,
        new_index: usize,
    ) {
        let mut ja = JitAssembler {
            a: Assembler::new(&mut self.buffer),
            machine: &self.machine,
            globals: &self.globals,
        };
        ja.a.set_pos(self.used);
        let retire_target = ja.a.get_pos(); // Evaluation order.
        self.retire_labels[old_index] =
            self.retire_labels[old_index].patch(&mut ja.a, retire_target);
        ja.lower_test_op(test_op, prec, &mut self.retire_labels[old_index]);
        for action in actions {
            ja.lower_action(action);
        }
        ja.a.const_jump(&mut self.fetch_labels[new_index]);
        self.used = ja.a.get_pos();
    }

    pub fn execute(mut self, state: M::State) -> (Self, M::State) {
        let index = self.states.get_index_of(&state).expect("invalid state");
        assert!(self.pool.len() >= self.globals.len());
        let pool = self.pool.as_mut_ptr();
        let (buffer, new_index) = self.buffer.execute(|bytes| {
            // FIXME: assert we are on x86_64 at compile time.
            let f: RunFn = unsafe { mem::transmute(&bytes[0]) };
            f(pool, index)
        }).expect("Couldn't change permissions");
        self.buffer = buffer;
        let new_state = self.states.get_index(new_index).expect("invalid index").clone();
        (self, new_state)
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    mod factorial {
        use super::code::*;
        use Action::*;
        use BinaryOp::*;
        use Precision::*;
        use R::*;

        #[derive(Debug, Clone, Hash, PartialEq, Eq)]
        pub enum State {Start, Loop, Return}

        #[derive(Debug, Clone, Hash, PartialEq, Eq)]
        pub enum Global {N, Result}

        impl super::code::Alias for () {}

        #[derive(Debug)]
        pub struct Machine;

        impl super::code::Machine for Machine {
            type State = State;
            type Global = Global;
            type Memory = ();
            
            fn get_code(&self, state: Self::State) ->
                Vec<(
                    (TestOp, Precision),
                    Vec<Action<Self::Memory, Self::Global>>,
                    Self::State,
                )>
            {
                match state {
                    State::Start => {vec![
                        ((TestOp::Always, P32), vec![
                            Constant(P32, RD, 1),
                            LoadGlobal(RA, Global::N),
                        ], State::Loop),
                    ]},
                    State::Loop => {vec![
                        ((TestOp::Eq(RA, 0), P32), vec![
                            StoreGlobal(RD, Global::Result),
                        ], State::Return),
                        ((TestOp::Ne(RA, 0), P32), vec![
                            Binary(Mul, P32, RD, RD, RA),
                            Constant(P32, RC, 1),
                            Binary(Sub, P32, RA, RA, RC),
                        ], State::Loop),
                    ]},
                    State::Return => {vec![]},
                }
            }

            fn initial_states(&self) -> Vec<Self::State> {
                vec![State::Start]
            }
        }
    }

    /** An amount of code space suitable for running tests. */
    pub const CODE_SIZE: usize = 1 << 20;

    #[test]
    pub fn factorial() {
        use factorial::*;
        use State::*;

        let mut jit = Jit::new(Machine, CODE_SIZE);

        // Check the `states` list.
        let expected: IndexSet<_> = vec![
            Start, Loop, Return,
        ]
        .into_iter()
        .collect();
        assert_eq!(jit.states(), &expected);

        // Run some "code".
        *jit.global(&Global::N) = 5;
        let (mut jit, final_state) = jit.execute(Start);
        assert_eq!(final_state, Return);
        assert_eq!(*jit.global(&Global::Result), 120);
    }

    #[test]
    pub fn startup_and_shutdown() {

    }
}
