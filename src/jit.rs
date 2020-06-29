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
    pub retire_labels: Vec<Label>,
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
        let mut retire_labels: Vec<Label> = (0..states.len()).map(|_| Label::new(None)).collect();
        for (index, &_) in states.iter().enumerate() {
            a.const_op(Cmp, R8, index as i32);
            a.jump_if(Condition::Z, true, &mut retire_labels[index]);
        }
        a.const_(RA, -1i32);

        // Assemble the function epilogue.
        let mut epilogue = Label::new(None);
        a.define(&mut epilogue);
        a.ret();

        // Construct the root labels. [TODO: Histories].
        for (index, _) in states.iter().enumerate() {
            a.define(&mut retire_labels[index]);
            a.const_(RA, index as i32);
            a.const_jump(&mut epilogue);
        }

        for (index, state) in states.iter().enumerate() {
            for (_test_op, _actions, _new_state) in machine.get_code(state.clone()) {
                let new_target = a.get_pos();
                retire_labels[index] = retire_labels[index].patch(&mut a, new_target);
                a.const_jump(&mut retire_labels[index]);
            }
        }

        // Return everything.
        let used = a.get_pos();
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
            "je near 0000000000000247h",
            "cmp r8d,1",
            "je near 000000000000024Dh",
            "cmp r8d,2",
            "je near 0000000000000487h",
            "cmp r8d,3",
            "je near 000000000000048Dh",
            "cmp r8d,4",
            "je near 00000000000004A5h",
            "cmp r8d,5",
            "je near 00000000000004BDh",
            "cmp r8d,6",
            "je near 00000000000004C9h",
            "cmp r8d,7",
            "je near 00000000000004D5h",
            "cmp r8d,8",
            "je near 00000000000004E1h",
            "cmp r8d,9",
            "je near 00000000000004EDh",
            "cmp r8d,0Ah",
            "je near 00000000000004F9h",
            "cmp r8d,0Bh",
            "je near 0000000000000505h",
            "cmp r8d,0Ch",
            "je near 000000000000050Bh",
            "cmp r8d,0Dh",
            "je near 0000000000000511h",
            "cmp r8d,0Eh",
            "je near 000000000000051Dh",
            "cmp r8d,0Fh",
            "je near 0000000000000529h",
            "cmp r8d,10h",
            "je near 0000000000000535h",
            "cmp r8d,11h",
            "je near 0000000000000541h",
            "cmp r8d,12h",
            "je near 000000000000054Dh",
            "cmp r8d,13h",
            "je near 0000000000000559h",
            "cmp r8d,14h",
            "je near 0000000000000565h",
            "cmp r8d,15h",
            "je near 0000000000000571h",
            "cmp r8d,16h",
            "je near 000000000000057Dh",
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
            "jmp 0000000000000133h",
            "jmp 0000000000000253h",
            "jmp 0000000000000259h",
            "jmp 000000000000025Fh",
            "jmp 0000000000000265h",
            "jmp 000000000000026Bh",
            "jmp 0000000000000271h",
            "jmp 0000000000000277h",
            "jmp 000000000000027Dh",
            "jmp 0000000000000283h",
            "jmp 0000000000000289h",
            "jmp 000000000000028Fh",
            "jmp 0000000000000295h",
            "jmp 000000000000029Bh",
            "jmp 00000000000002A1h",
            "jmp 00000000000002A7h",
            "jmp 00000000000002ADh",
            "jmp 00000000000002B3h",
            "jmp 00000000000002B9h",
            "jmp 00000000000002BFh",
            "jmp 00000000000002C5h",
            "jmp 00000000000002CBh",
            "jmp 00000000000002D1h",
            "jmp 00000000000002D7h",
            "jmp 00000000000002DDh",
            "jmp 00000000000002E3h",
            "jmp 00000000000002E9h",
            "jmp 00000000000002EFh",
            "jmp 00000000000002F5h",
            "jmp 00000000000002FBh",
            "jmp 0000000000000301h",
            "jmp 0000000000000307h",
            "jmp 000000000000030Dh",
            "jmp 0000000000000313h",
            "jmp 0000000000000319h",
            "jmp 000000000000031Fh",
            "jmp 0000000000000325h",
            "jmp 000000000000032Bh",
            "jmp 0000000000000331h",
            "jmp 0000000000000337h",
            "jmp 000000000000033Dh",
            "jmp 0000000000000343h",
            "jmp 0000000000000349h",
            "jmp 000000000000034Fh",
            "jmp 0000000000000355h",
            "jmp 000000000000035Bh",
            "jmp 0000000000000361h",
            "jmp 0000000000000367h",
            "jmp 000000000000036Dh",
            "jmp 0000000000000373h",
            "jmp 0000000000000379h",
            "jmp 000000000000037Fh",
            "jmp 0000000000000385h",
            "jmp 000000000000038Bh",
            "jmp 0000000000000391h",
            "jmp 0000000000000397h",
            "jmp 000000000000039Dh",
            "jmp 00000000000003A3h",
            "jmp 00000000000003A9h",
            "jmp 00000000000003AFh",
            "jmp 00000000000003B5h",
            "jmp 00000000000003BBh",
            "jmp 00000000000003C1h",
            "jmp 00000000000003C7h",
            "jmp 00000000000003CDh",
            "jmp 00000000000003D3h",
            "jmp 00000000000003D9h",
            "jmp 00000000000003DFh",
            "jmp 00000000000003E5h",
            "jmp 00000000000003EBh",
            "jmp 00000000000003F1h",
            "jmp 00000000000003F7h",
            "jmp 00000000000003FDh",
            "jmp 0000000000000403h",
            "jmp 0000000000000409h",
            "jmp 000000000000040Fh",
            "jmp 0000000000000415h",
            "jmp 000000000000041Bh",
            "jmp 0000000000000421h",
            "jmp 0000000000000427h",
            "jmp 000000000000042Dh",
            "jmp 0000000000000433h",
            "jmp 0000000000000439h",
            "jmp 000000000000043Fh",
            "jmp 0000000000000445h",
            "jmp 000000000000044Bh",
            "jmp 0000000000000451h",
            "jmp 0000000000000457h",
            "jmp 000000000000045Dh",
            "jmp 0000000000000463h",
            "jmp 0000000000000469h",
            "jmp 000000000000046Fh",
            "jmp 0000000000000475h",
            "jmp 000000000000047Bh",
            "jmp 0000000000000481h",
            "jmp 000000000000013Fh",
            "jmp 000000000000014Bh",
            "jmp 0000000000000493h",
            "jmp 0000000000000499h",
            "jmp 000000000000049Fh",
            "jmp 0000000000000157h",
            "jmp 00000000000004ABh",
            "jmp 00000000000004B1h",
            "jmp 00000000000004B7h",
            "jmp 0000000000000163h",
            "jmp 00000000000004C3h",
            "jmp 000000000000016Fh",
            "jmp 00000000000004CFh",
            "jmp 000000000000017Bh",
            "jmp 00000000000004DBh",
            "jmp 0000000000000187h",
            "jmp 00000000000004E7h",
            "jmp 0000000000000193h",
            "jmp 00000000000004F3h",
            "jmp 000000000000019Fh",
            "jmp 00000000000004FFh",
            "jmp 00000000000001ABh",
            "jmp 00000000000001B7h",
            "jmp 00000000000001C3h",
            "jmp 0000000000000517h",
            "jmp 00000000000001CFh",
            "jmp 0000000000000523h",
            "jmp 00000000000001DBh",
            "jmp 000000000000052Fh",
            "jmp 00000000000001E7h",
            "jmp 000000000000053Bh",
            "jmp 00000000000001F3h",
            "jmp 0000000000000547h",
            "jmp 00000000000001FFh",
            "jmp 0000000000000553h",
            "jmp 000000000000020Bh",
            "jmp 000000000000055Fh",
            "jmp 0000000000000217h",
            "jmp 000000000000056Bh",
            "jmp 0000000000000223h",
            "jmp 0000000000000577h",
            "jmp 000000000000022Fh",
            "jmp 0000000000000583h",
            "jmp 000000000000023Bh",
        ]).unwrap();
    }

    #[test]
    pub fn startup_and_shutdown() {

    }
}