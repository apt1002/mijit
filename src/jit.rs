use std::{mem};

use indexmap::IndexSet;

use super::{Buffer, code, control_flow, x86_64};
use control_flow::{Machine};
use x86_64::*;
use Register::*;
use BinaryOp::*;
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

/**
 * A collection of x86_64::Patch, all with the same target.
 */
pub struct Patches {
    patches: Vec<Patch>,
    target: Option<usize>,
}

impl Patches {
    pub fn new(target: Option<usize>) -> Self {
        Patches {patches: Vec::new(), target: target}
    }

    pub fn patch(&mut self, a: &mut Assembler) -> Option<usize> {
        let target = a.label();
        let old_target = self.target;
        for &mut patch in &mut self.patches {
            assert_eq!(a.patch(patch, target), old_target);
        }
        self.target = Some(target);
        old_target
    }

    pub fn jump_if(&mut self, a: &mut Assembler, cc: Condition, is_true: bool) {
        self.patches.push(a.jump_if(cc, is_true, self.target));
    }

    pub fn const_jump(&mut self, a: &mut Assembler) {
        self.patches.push(a.const_jump(self.target));
    }

    pub fn const_call(&mut self, a: &mut Assembler) {
        self.patches.push(a.const_call(self.target));
    }
}

pub struct History<A: control_flow::Address> {
    /** The test which must pass in order to execute `fetch`. */
    pub test: code::TestOp,
    /** The code for the unique "fetch" transition to this History. */
    pub fetch: Vec<code::Action<A>>,
    /** The interface from `fetch` to `retire`. */
    pub convention: Convention,
    /** The code for the unique "retire" transition from this History. */
    pub retire: Vec<code::Action<A>>,
    /** All jump instructions whose target is `retire`. */
    pub retire_jumps: Vec<Patch>,
}

/**
 * The type of the generated code.
 *  - current_index - the index of the current M::State in `states`.
 * Returns:
 *  - new_index - updated `current_index`.
 */
type RunFn = extern "C" fn(
    /* current_index */  usize,
) -> /* new_index */ usize;

pub struct Jit<M: Machine> {
    states: IndexSet<M::State>,
    buffer: Buffer,
    used: usize,
}

impl<M: Machine> Jit<M> {
    pub fn new(machine: M, code_size: usize) -> Self {
        // Enumerate the reachable states in FIFO order.
        let mut states: IndexSet<_> = machine.initial_states().into_iter().collect();
        let mut done = 0;
        while let Some(state) = states.get_index(done) {
            for (_test_op, _actions, new_state) in machine.get_code(state.clone()) {
                let (_, _) = states.insert_full(new_state);
            }
            done += 1;
        }

        // Assemble the function prologue.
        let mut buffer = Buffer::new(code_size).expect("couldn't allocate memory");
        let mut a = Assembler::new(&mut buffer);
        let mut retire_jumps: Vec<Patches> = (0..states.len()).map(|_| Patches::new(None)).collect();
        for (index, &_) in states.iter().enumerate() {
            a.const_op(Cmp, R8, index as i32);
            retire_jumps[index].jump_if(&mut a, Condition::Z, true);
        }
        a.const_(RA, -1i32);

        // Assemble the function epilogue.
        let epilogue = a.label();
        a.ret();

        // Construct the root labels. [TODO: Histories].
        for (index, _) in states.iter().enumerate() {
            assert_eq!(retire_jumps[index].patch(&mut a), None);
            a.const_(RA, index as i32);
            a.const_jump(Some(epilogue));
        }

        for (index, state) in states.iter().enumerate() {
            for (test_op, actions, new_state) in machine.get_code(state.clone()) {
                let old_retire_label = retire_jumps[index].patch(&mut a);
                retire_jumps[index] = Patches::new(old_retire_label);
                retire_jumps[index].const_jump(&mut a);
            }
        }

        // Return everything.
        let used = a.label();
        Jit {states, buffer, used}
    }

    pub fn used(&self) -> usize {
        self.used
    }

    pub fn states(&self) -> &IndexSet<M::State> {
        &self.states
    }

    pub fn execute(mut self, state: M::State) -> (Self, M::State) {
        let index = self.states.get_index_of(&state).expect("invalid state");
        let (buffer, new_index) = self.buffer.execute(|bytes| {
            // FIXME: assert we are on x86_64 at compile time.
            let f: RunFn = unsafe { mem::transmute(&bytes[0]) };
            f(index)
        }).expect("Couldn't change permissions");
        self.buffer = buffer;
        let new_state = self.states.get_index(new_index).expect("invalid index").clone();
        (self, new_state)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use super::x86_64::tests::{disassemble};

    const CODE_SIZE: usize = 1 << 20;

    #[test]
    pub fn beetle() {
        use super::super::{beetle};
        use beetle::State::*;
        let jit = Jit::new(beetle::Machine, CODE_SIZE);

        // Check the `states` list.
        let expected: IndexSet<_> = vec![
            Root, Dispatch, Next, Pick, Roll, Qdup, Abs, Max, Min, Lshift, Rshift, Branch, Branchi,
            Qbranch, Qbranchi, Loop, Loopi, Ploop, Ploopi, Ploopp, Ploopm, Ploopip, Ploopim,
        ]
        .into_iter()
        .collect();
        assert_eq!(jit.states(), &expected);

        // Disassemble the prologue and epilogue.
        disassemble(&jit.buffer[..jit.used], vec![
            "cmp r8d,0",
            "je near 0000000000000133h",
            "cmp r8d,1",
            "je near 000000000000013Fh",
            "cmp r8d,2",
            "je near 000000000000014Bh",
            "cmp r8d,3",
            "je near 0000000000000157h",
            "cmp r8d,4",
            "je near 0000000000000163h",
            "cmp r8d,5",
            "je near 000000000000016Fh",
            "cmp r8d,6",
            "je near 000000000000017Bh",
            "cmp r8d,7",
            "je near 0000000000000187h",
            "cmp r8d,8",
            "je near 0000000000000193h",
            "cmp r8d,9",
            "je near 000000000000019Fh",
            "cmp r8d,0Ah",
            "je near 00000000000001ABh",
            "cmp r8d,0Bh",
            "je near 00000000000001B7h",
            "cmp r8d,0Ch",
            "je near 00000000000001C3h",
            "cmp r8d,0Dh",
            "je near 00000000000001CFh",
            "cmp r8d,0Eh",
            "je near 00000000000001DBh",
            "cmp r8d,0Fh",
            "je near 00000000000001E7h",
            "cmp r8d,10h",
            "je near 00000000000001F3h",
            "cmp r8d,11h",
            "je near 00000000000001FFh",
            "cmp r8d,12h",
            "je near 000000000000020Bh",
            "cmp r8d,13h",
            "je near 0000000000000217h",
            "cmp r8d,14h",
            "je near 0000000000000223h",
            "cmp r8d,15h",
            "je near 000000000000022Fh",
            "cmp r8d,16h",
            "je near 000000000000023Bh",
            "mov eax,0FFFFFFFFh",
            "ret",
            "mov eax,0",
            "jmp 0000000000000131h",
            "mov eax,1",
            "jmp 0000000000000131h",
            "mov eax,2",
            "jmp 0000000000000131h",
            "mov eax,3",
            "jmp 0000000000000131h",
            "mov eax,4",
            "jmp 0000000000000131h",
            "mov eax,5",
            "jmp 0000000000000131h",
            "mov eax,6",
            "jmp 0000000000000131h",
            "mov eax,7",
            "jmp 0000000000000131h",
            "mov eax,8",
            "jmp 0000000000000131h",
            "mov eax,9",
            "jmp 0000000000000131h",
            "mov eax,0Ah",
            "jmp 0000000000000131h",
            "mov eax,0Bh",
            "jmp 0000000000000131h",
            "mov eax,0Ch",
            "jmp 0000000000000131h",
            "mov eax,0Dh",
            "jmp 0000000000000131h",
            "mov eax,0Eh",
            "jmp 0000000000000131h",
            "mov eax,0Fh",
            "jmp 0000000000000131h",
            "mov eax,10h",
            "jmp 0000000000000131h",
            "mov eax,11h",
            "jmp 0000000000000131h",
            "mov eax,12h",
            "jmp 0000000000000131h",
            "mov eax,13h",
            "jmp 0000000000000131h",
            "mov eax,14h",
            "jmp 0000000000000131h",
            "mov eax,15h",
            "jmp 0000000000000131h",
            "mov eax,16h",
            "jmp 0000000000000131h",
        ]).unwrap();
    }

    #[test]
    pub fn startup_and_shutdown() {

    }
}
