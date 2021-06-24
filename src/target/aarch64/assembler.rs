use super::{buffer};
use buffer::{Buffer};

/**
 * All AArch64 registers. For our purposes, `IP0` (=`R16`) and `IP1` (=`R17`)
 * are ordinary registers. We also include R18, despite [ARM's advice].
 *
 * [ARM's advice]: https://github.com/ARM-software/abi-aa/blob/2bcab1e3b22d55170c563c3c7940134089176746/aapcs64/aapcs64.rst#general-purpose-registers
 *
 * All register names include a leading `R`. This is not intended to imply
 * anything about the operand width, which is specified in another way.
 */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
#[allow(clippy::upper_case_acronyms)]
pub enum Register {
    R0  = 0x00, R1  = 0x01, R2  = 0x02, R3  = 0x03, R4  = 0x04, R5  = 0x05, R6  = 0x06, R7  = 0x07,
    R8  = 0x08, R9  = 0x09, R10 = 0x0A, R11 = 0x0B, R12 = 0x0C, R13 = 0x0D, R14 = 0x0E, R15 = 0x0F,
    R16 = 0x10, R17 = 0x11, R18 = 0x12, R19 = 0x13, R20 = 0x14, R21 = 0x15, R22 = 0x16, R23 = 0x17,
    R24 = 0x18, R25 = 0x19, R26 = 0x1A, R27 = 0x1B, R28 = 0x1C, RFP = 0x1D, RLR = 0x1E, RZR = 0x1F,
}

use Register::*;

/**
 * The stack pointer register `RSP` shares an encoding with the zero register
 * `RZR`.
 */
pub const RSP: Register = RZR;

//-----------------------------------------------------------------------------

/** All AArch64 conditions except `AL` (and `NV`). */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
#[allow(clippy::upper_case_acronyms)]
pub enum Condition {
    EQ = 0x0, NE = 0x1,
    CS = 0x2, CC = 0x3,
    MI = 0x4, PL = 0x5,
    VS = 0x6, VC = 0x7,
    HI = 0x8, LS = 0x9,
    GE = 0xA, LT = 0xB,
    GT = 0xC, LE = 0xD,
}

//-----------------------------------------------------------------------------

/**
 * An assembler, implementing a regularish subset of aarch64.
 */
pub struct Assembler<B: Buffer> {
    /// The area we're filling with code.
    buffer: B,
}

impl<B: Buffer> Assembler<B> {
    /** Construct an Assembler that writes to `buffer`. */
    pub fn new() -> Self {
        Assembler {buffer: B::new()}
    }

    /** Apply `callback` to the contained [`Buffer`]. */
    pub fn use_buffer<T>(
        mut self,
        callback: impl FnOnce(B) -> std::io::Result<(B, T)>,
    ) -> std::io::Result<(Self, T)> {
        let (buffer, ret) = callback(self.buffer)?;
        self.buffer = buffer;
        Ok((self, ret))
    }

    /** Get the assembly pointer. */
    pub fn get_pos(&self) -> usize {
        self.buffer.get_pos()
    }

    /** Set the assembly pointer. */
    pub fn set_pos(&mut self, pos: usize) {
        self.buffer.set_pos(pos);
    }
}

impl<B: Buffer> Default for Assembler<B> {
    fn default() -> Self {
        Self::new()
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    use std::cmp::{min, max};

    use buffer::{VecU8};

    /**
     * Disassemble the code that has been assembled by `a` as if the [`Buffer`]
     * were at offset 0.
     *  - `a` - an assembler which has generated some code.
     *  - `start_address` - the address (relative to the `Buffer`) at which to
     *    start disassembling.
     *  - `expected` - the expected disassembly of the code.
     */
    pub fn disassemble<B: Buffer>(a: &Assembler<B>, start_address: usize, expected: Vec<&str>)
    -> Result<(), Vec<String>> {
        // Disassemble the code.
        let code_bytes = &a.buffer[start_address..a.get_pos()];
        let mut pcs = Vec::new();
        let mut observed = Vec::new();
        for maybe_decoded in bad64::disasm(code_bytes, start_address as u64) {
            let (pc, asm) = match maybe_decoded {
                Ok(instruction) => (instruction.address(), format!("{}", instruction)),
                Err(error) => (error.address(), format!("{:?}", error)),
            };
            pcs.push(pc);
            observed.push(asm);
        }
        // Search for differences.
        let mut error = false;
        for i in 0..max(expected.len(), observed.len()) {
            let e_line = if i < expected.len() { &expected[i] } else { "missing" };
            let o_line = if i < observed.len() { &observed[i] } else { "missing" };
            if e_line != o_line {
                let instruction_bytes = &a.buffer[(pcs[i] as usize)..a.get_pos()];
                let instruction_bytes = &instruction_bytes[..min(instruction_bytes.len(), 4)];
                let hex_dump = instruction_bytes.iter().rev().map(
                    |b| format!("{:02X}", b)
                ).collect::<Vec<String>>().join(" ");
                println!("Difference in line {}", i+1);
                println!("{:016X}   {:>32}   {}", pcs[i], hex_dump, o_line);
                println!("{:>16}   {:>32}   {}", "Expected", "", e_line);
                error = true;
            }
        }
        if error { Err(observed) } else { Ok(()) }
    }

    #[test]
    fn test_disassemble() {
        let mut a = Assembler::<VecU8>::new();
        a.buffer.write(0x912AA3E0, 4);
        a.buffer.write(0x9B007C00, 4);
        disassemble(&a, 0, vec![
            "add x0, sp, #0xaa8",
            "mul x0, x0, x0",
        ]).unwrap();
    }
}
