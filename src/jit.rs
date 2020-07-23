use std::{mem};
use indexmap::{IndexSet};

use super::{Buffer, code, x86_64};
use code::{Action, TestOp, Machine};
use x86_64::*;
use Register::*;
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
        false_label: &mut Label,
    ) {
        match test_op {
            TestOp::Bits(discriminant, mask, value) => {
                self.a.const_(RC, mask as i32);
                self.a.op(And, RC, discriminant);
                self.a.const_op(Cmp, RC, value as i32);
                self.a.jump_if(Condition::Z, false, false_label);
            },
            TestOp::Lt(discriminant, value) => {
                self.a.const_op(Cmp, discriminant, value as i32);
                self.a.jump_if(Condition::L, false, false_label);
            },
            TestOp::Ge(discriminant, value) => {
                self.a.const_op(Cmp, discriminant, value as i32);
                self.a.jump_if(Condition::GE, false, false_label);
            },
            TestOp::Ult(discriminant, value) => {
                self.a.const_op(Cmp, discriminant, value as i32);
                self.a.jump_if(Condition::B, false, false_label);
            },
            TestOp::Uge(discriminant, value) => {
                self.a.const_op(Cmp, discriminant, value as i32);
                self.a.jump_if(Condition::AE, false, false_label);
            },
            TestOp::Eq(discriminant, value) => {
                self.a.const_op(Cmp, discriminant, value as i32);
                self.a.jump_if(Condition::Z, false, false_label);
            },
            TestOp::Ne(discriminant, value) => {
                self.a.const_op(Cmp, discriminant, value as i32);
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
        dest: code::R,
        src: code::R,
    ) {
        match unary_op {
            code::UnaryOp::Abs => {
                self.a.move_(RC, src);
                self.a.const_(dest, 0);
                self.a.op(Sub, dest, RC);
                self.a.move_if(Condition::L, true, dest, RC);
            },
            code::UnaryOp::Negate => {
                self.a.move_(RC, src);
                self.a.const_(dest, 0);
                self.a.op(Sub, dest, RC);
            },
            code::UnaryOp::Not => {
                self.a.move_(dest, src);
                self.a.const_op(Xor, dest, -1);
            },
        };
    }

    /**
     * Assemble code to perform the given `binary_op`.
     */
    fn lower_binary_op(
        &mut self,
        binary_op: code::BinaryOp,
        dest: code::R,
        src1: code::R,
        src2: code::R,
    ) {
        match binary_op {
            code::BinaryOp::Add => {
                self.a.move_(dest, src1);
                self.a.op(Add, dest, src2);
            },
            code::BinaryOp::Sub => {
                self.a.move_(dest, src1);
                self.a.op(Sub, dest, src2);
            },
            code::BinaryOp::Mul => {
                self.a.move_(dest, src1);
                self.a.mul(dest, src2);
            },
            code::BinaryOp::Lsl => {
                self.a.move_(dest, src1);
                self.a.move_(RC, src2);
                self.a.shift(Shl, dest);
            },
            code::BinaryOp::Lsr => {
                self.a.move_(dest, src1);
                self.a.move_(RC, src2);
                self.a.shift(Shr, dest);
            },
            code::BinaryOp::Asr => {
                self.a.move_(dest, src1);
                self.a.move_(RC, src2);
                self.a.shift(Sar, dest);
            },
            code::BinaryOp::And => {
                self.a.move_(dest, src1);
                self.a.op(And, dest, src2);
            },
            code::BinaryOp::Or => {
                self.a.move_(dest, src1);
                self.a.op(Or, dest, src2);
            },
            code::BinaryOp::Xor => {
                self.a.move_(dest, src1);
                self.a.op(Xor, dest, src2);
            },
            code::BinaryOp::Lt => {
                self.a.const_(RC, -1);
                self.a.const_(dest, 0);
                self.a.op(Cmp, src1, src2);
                self.a.move_if(Condition::L, true, dest, RC);
            },
            code::BinaryOp::Ult => {
                self.a.const_(RC, -1);
                self.a.const_(dest, 0);
                self.a.op(Cmp, src1, src2);
                self.a.move_if(Condition::B, true, dest, RC);
            },
            code::BinaryOp::Eq => {
                self.a.const_(RC, -1);
                self.a.const_(dest, 0);
                self.a.op(Cmp, src1, src2);
                self.a.move_if(Condition::Z, true, dest, RC);
            },
            code::BinaryOp::Max => {
                self.a.op(Cmp, src1, src2);
                self.a.move_(dest, src2);
                self.a.move_if(Condition::G, true, dest, src1);
            },
            code::BinaryOp::Min => {
                self.a.op(Cmp, src1, src2);
                self.a.move_(dest, src2);
                self.a.move_if(Condition::L, true, dest, src1);
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
            Action::Constant(dest, value) => {
                self.a.const_(dest, value as i32);
            },
            Action::Move(dest, src) => {
                self.a.move_(dest, src);
            },
            Action::Unary(op, dest, src) => {
                self.lower_unary_op(op, dest, src);
            },
            Action::Binary(op, dest, src1, src2) => {
                self.lower_binary_op(op, dest, src1, src2);
            },
            Action::Division(_op, _, _, _, _) => {
                panic!("FIXME: Don't know how to assemble div");
            },
            Action::LoadGlobal(dest, global) => {
                let offset = self.global_offset(&global);
                self.a.load(dest, (R8, offset));
            },
            Action::StoreGlobal(src, global) => {
                let offset = self.global_offset(&global);
                self.a.store((R8, offset), src);
            },
            Action::Load(dest, mloc) => {
                let (addr, width) = Self::lower_memory_location(mloc);
                self.a.load_narrow(width, dest, (addr, 0));
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
    retire_labels: Vec<Label>,
    /** The mmapped memory buffer containing the compiled code. */
    buffer: Buffer,
    /** The number of bytes of `buffer` already occupied. */
    used: usize,
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
        let mut retire_labels: Vec<Label> = (0..states.len()).map(|_| Label::new(None)).collect();
        let mut buffer = Buffer::new(code_size).expect("couldn't allocate memory");
        let mut a = Assembler::new(&mut buffer);
        for (index, &_) in states.iter().enumerate() {
            a.const_op(Cmp, R8, index as i32);
            a.jump_if(Condition::Z, true, &mut retire_labels[index]);
        }
        a.const_(RA, -1i32);

        // Assemble the function epilogue.
        let mut epilogue = Label::new(None);
        a.define(&mut epilogue);
        a.ret();

        // Construct the root labels.
        for (index, _) in states.iter().enumerate() {
            a.define(&mut retire_labels[index]);
            a.const_(RA, index as i32);
            a.const_jump(&mut epilogue);
        }

        // Construct the Jit.
        let used = a.get_pos();
        let mut jit = Jit {machine, states, globals, retire_labels, buffer, used};

        // Construct the root Histories.
        let all_states: Vec<_> = jit.states.iter().cloned().collect();
        for old_state in all_states {
            for (test_op, actions, new_state) in jit.machine.get_code(old_state.clone()) {
                let old_index = jit.states.get_index_of(&old_state).unwrap();
                let new_index = jit.states.get_index_of(&new_state).unwrap();
                jit.insert_history(old_index, test_op, actions, new_index);
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
        ja.lower_test_op(test_op, &mut self.retire_labels[old_index]);
        for action in actions {
            ja.lower_action(action);
        }
        ja.a.const_jump(&mut self.retire_labels[new_index]);
        self.used = ja.a.get_pos();
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

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;
    use super::x86_64::tests::{disassemble};

    const CODE_SIZE: usize = 1 << 20;

    #[test]
    #[ignore]
    pub fn beetle() {
        use super::super::{beetle};
        use beetle::State::*;
        let jit = Jit::new(beetle::Machine, CODE_SIZE);

        // Check the `states` list.
        let expected: IndexSet<_> = vec![
            Root, Dispatch, Next, Pick, Roll, Qdup, Lshift, Rshift, Branch, Branchi,
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
