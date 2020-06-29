use std::{mem};

use indexmap::IndexSet;

use super::{Assembler, Buffer, code, control_flow, x86_64};
use control_flow::{Machine};
use x86_64::*;
use Register::*;
use BinaryOp::*;
use Condition;

/**
 * Represents the convention by which code before some label passes values
 * to code after the label. The concept is similar to a calling convention,
 * but it's for a jump, not a call.
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
pub struct Convention;

pub struct History<A: control_flow::Address> {
    pub test: code::TestOp,
    pub fetch: Vec<code::Action<A>>,
    pub calling_convention: Convention,
    pub register: code::R,
    pub retire: Vec<code::Action<A>>,
}

pub struct Jit<M: Machine> {
    states: IndexSet<M::State>,
    buffer: Buffer,
    used: usize,
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
        let mut cases: Vec<Patch> = Vec::new();
        for (index, &_) in states.iter().enumerate() {
            a.const_op(Cmp, R8, index as i32);
            let patch = a.jump_if(Condition::Z, true, None);
            cases.push(patch);
        }
        a.const_(RA, -1i32);

        // Assemble the function epilogue.
        let epilogue = a.label();
        a.ret();

        // Construct the root Histories.
        for (index, &_) in states.iter().enumerate() {
            a.patch(cases[index], a.label());
            a.const_(RA, index as i32);
            a.const_jump(Some(epilogue));
        }

        // Return everything.
        let used = a.label();
        Jit {states, buffer, used}
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
        assert_eq!(disassemble(&jit.buffer[..jit.used], 0), vec![
            "0000000000000000               00 00 00 00 F8 81 41   cmp r8d,0",
            "0000000000000007                  00 00 01 26 84 0F   je near 0000000000000133h",
            "000000000000000D               00 00 00 01 F8 81 41   cmp r8d,1",
            "0000000000000014                  00 00 01 25 84 0F   je near 000000000000013Fh",
            "000000000000001A               00 00 00 02 F8 81 41   cmp r8d,2",
            "0000000000000021                  00 00 01 24 84 0F   je near 000000000000014Bh",
            "0000000000000027               00 00 00 03 F8 81 41   cmp r8d,3",
            "000000000000002E                  00 00 01 23 84 0F   je near 0000000000000157h",
            "0000000000000034               00 00 00 04 F8 81 41   cmp r8d,4",
            "000000000000003B                  00 00 01 22 84 0F   je near 0000000000000163h",
            "0000000000000041               00 00 00 05 F8 81 41   cmp r8d,5",
            "0000000000000048                  00 00 01 21 84 0F   je near 000000000000016Fh",
            "000000000000004E               00 00 00 06 F8 81 41   cmp r8d,6",
            "0000000000000055                  00 00 01 20 84 0F   je near 000000000000017Bh",
            "000000000000005B               00 00 00 07 F8 81 41   cmp r8d,7",
            "0000000000000062                  00 00 01 1F 84 0F   je near 0000000000000187h",
            "0000000000000068               00 00 00 08 F8 81 41   cmp r8d,8",
            "000000000000006F                  00 00 01 1E 84 0F   je near 0000000000000193h",
            "0000000000000075               00 00 00 09 F8 81 41   cmp r8d,9",
            "000000000000007C                  00 00 01 1D 84 0F   je near 000000000000019Fh",
            "0000000000000082               00 00 00 0A F8 81 41   cmp r8d,0Ah",
            "0000000000000089                  00 00 01 1C 84 0F   je near 00000000000001ABh",
            "000000000000008F               00 00 00 0B F8 81 41   cmp r8d,0Bh",
            "0000000000000096                  00 00 01 1B 84 0F   je near 00000000000001B7h",
            "000000000000009C               00 00 00 0C F8 81 41   cmp r8d,0Ch",
            "00000000000000A3                  00 00 01 1A 84 0F   je near 00000000000001C3h",
            "00000000000000A9               00 00 00 0D F8 81 41   cmp r8d,0Dh",
            "00000000000000B0                  00 00 01 19 84 0F   je near 00000000000001CFh",
            "00000000000000B6               00 00 00 0E F8 81 41   cmp r8d,0Eh",
            "00000000000000BD                  00 00 01 18 84 0F   je near 00000000000001DBh",
            "00000000000000C3               00 00 00 0F F8 81 41   cmp r8d,0Fh",
            "00000000000000CA                  00 00 01 17 84 0F   je near 00000000000001E7h",
            "00000000000000D0               00 00 00 10 F8 81 41   cmp r8d,10h",
            "00000000000000D7                  00 00 01 16 84 0F   je near 00000000000001F3h",
            "00000000000000DD               00 00 00 11 F8 81 41   cmp r8d,11h",
            "00000000000000E4                  00 00 01 15 84 0F   je near 00000000000001FFh",
            "00000000000000EA               00 00 00 12 F8 81 41   cmp r8d,12h",
            "00000000000000F1                  00 00 01 14 84 0F   je near 000000000000020Bh",
            "00000000000000F7               00 00 00 13 F8 81 41   cmp r8d,13h",
            "00000000000000FE                  00 00 01 13 84 0F   je near 0000000000000217h",
            "0000000000000104               00 00 00 14 F8 81 41   cmp r8d,14h",
            "000000000000010B                  00 00 01 12 84 0F   je near 0000000000000223h",
            "0000000000000111               00 00 00 15 F8 81 41   cmp r8d,15h",
            "0000000000000118                  00 00 01 11 84 0F   je near 000000000000022Fh",
            "000000000000011E               00 00 00 16 F8 81 41   cmp r8d,16h",
            "0000000000000125                  00 00 01 10 84 0F   je near 000000000000023Bh",
            "000000000000012B                  FF FF FF FF B8 40   mov eax,0FFFFFFFFh",
            "0000000000000131                              C3 40   ret",
            "0000000000000133                  00 00 00 00 B8 40   mov eax,0",
            "0000000000000139                  FF FF FF F2 E9 40   jmp 0000000000000131h",
            "000000000000013F                  00 00 00 01 B8 40   mov eax,1",
            "0000000000000145                  FF FF FF E6 E9 40   jmp 0000000000000131h",
            "000000000000014B                  00 00 00 02 B8 40   mov eax,2",
            "0000000000000151                  FF FF FF DA E9 40   jmp 0000000000000131h",
            "0000000000000157                  00 00 00 03 B8 40   mov eax,3",
            "000000000000015D                  FF FF FF CE E9 40   jmp 0000000000000131h",
            "0000000000000163                  00 00 00 04 B8 40   mov eax,4",
            "0000000000000169                  FF FF FF C2 E9 40   jmp 0000000000000131h",
            "000000000000016F                  00 00 00 05 B8 40   mov eax,5",
            "0000000000000175                  FF FF FF B6 E9 40   jmp 0000000000000131h",
            "000000000000017B                  00 00 00 06 B8 40   mov eax,6",
            "0000000000000181                  FF FF FF AA E9 40   jmp 0000000000000131h",
            "0000000000000187                  00 00 00 07 B8 40   mov eax,7",
            "000000000000018D                  FF FF FF 9E E9 40   jmp 0000000000000131h",
            "0000000000000193                  00 00 00 08 B8 40   mov eax,8",
            "0000000000000199                  FF FF FF 92 E9 40   jmp 0000000000000131h",
            "000000000000019F                  00 00 00 09 B8 40   mov eax,9",
            "00000000000001A5                  FF FF FF 86 E9 40   jmp 0000000000000131h",
            "00000000000001AB                  00 00 00 0A B8 40   mov eax,0Ah",
            "00000000000001B1                  FF FF FF 7A E9 40   jmp 0000000000000131h",
            "00000000000001B7                  00 00 00 0B B8 40   mov eax,0Bh",
            "00000000000001BD                  FF FF FF 6E E9 40   jmp 0000000000000131h",
            "00000000000001C3                  00 00 00 0C B8 40   mov eax,0Ch",
            "00000000000001C9                  FF FF FF 62 E9 40   jmp 0000000000000131h",
            "00000000000001CF                  00 00 00 0D B8 40   mov eax,0Dh",
            "00000000000001D5                  FF FF FF 56 E9 40   jmp 0000000000000131h",
            "00000000000001DB                  00 00 00 0E B8 40   mov eax,0Eh",
            "00000000000001E1                  FF FF FF 4A E9 40   jmp 0000000000000131h",
            "00000000000001E7                  00 00 00 0F B8 40   mov eax,0Fh",
            "00000000000001ED                  FF FF FF 3E E9 40   jmp 0000000000000131h",
            "00000000000001F3                  00 00 00 10 B8 40   mov eax,10h",
            "00000000000001F9                  FF FF FF 32 E9 40   jmp 0000000000000131h",
            "00000000000001FF                  00 00 00 11 B8 40   mov eax,11h",
            "0000000000000205                  FF FF FF 26 E9 40   jmp 0000000000000131h",
            "000000000000020B                  00 00 00 12 B8 40   mov eax,12h",
            "0000000000000211                  FF FF FF 1A E9 40   jmp 0000000000000131h",
            "0000000000000217                  00 00 00 13 B8 40   mov eax,13h",
            "000000000000021D                  FF FF FF 0E E9 40   jmp 0000000000000131h",
            "0000000000000223                  00 00 00 14 B8 40   mov eax,14h",
            "0000000000000229                  FF FF FF 02 E9 40   jmp 0000000000000131h",
            "000000000000022F                  00 00 00 15 B8 40   mov eax,15h",
            "0000000000000235                  FF FF FE F6 E9 40   jmp 0000000000000131h",
            "000000000000023B                  00 00 00 16 B8 40   mov eax,16h",
            "0000000000000241                  FF FF FE EA E9 40   jmp 0000000000000131h",
        ]);
    }
}
