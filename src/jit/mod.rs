use indexmap::{IndexSet};

use super::{Buffer, code, x86_64};
use x86_64::*;
use code::{Action, TestOp, Machine, Precision};
use Register::*;
use Precision::*;
use BinaryOp::*;

mod assembler;
use assembler::{Lowerer};

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
    pub fetch: Vec<Action<M::Global>>,
    /** The interface from `fetch` to `retire`. */
    pub convention: Convention,
    /** The code for the unique "retire" transition from this History. */
    pub retire: Vec<Action<M::Global>>,
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
        actions: Vec<Action<M::Global>>,
        new_index: usize,
    ) {
        let mut lo = Lowerer {
            a: Assembler::new(&mut self.buffer),
            machine: &self.machine,
            globals: &self.globals,
        };
        lo.a.set_pos(self.used);
        let retire_target = lo.a.get_pos(); // Evaluation order.
        self.retire_labels[old_index] =
            self.retire_labels[old_index].patch(&mut lo.a, retire_target);
        lo.lower_test_op(test_op, prec, &mut self.retire_labels[old_index]);
        for action in actions {
            lo.lower_action(action);
        }
        lo.a.const_jump(&mut self.fetch_labels[new_index]);
        self.used = lo.a.get_pos();
    }

    pub fn execute(mut self, state: M::State) -> (Self, M::State) {
        let index = self.states.get_index_of(&state).expect("invalid state");
        assert!(self.pool.len() >= self.globals.len());
        let pool = self.pool.as_mut_ptr();
        let (buffer, new_index) = self.buffer.execute(|bytes| {
            // FIXME: assert we are on x86_64 at compile time.
            let f: RunFn = unsafe { std::mem::transmute(&bytes[0]) };
            f(pool, index)
        }).expect("Couldn't change permissions");
        self.buffer = buffer;
        let new_state = self.states.get_index(new_index).expect("invalid index").clone();
        (self, new_state)
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod factorial;

#[cfg(test)]
pub mod tests {
    use super::*;

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
}
