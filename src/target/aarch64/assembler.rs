use super::{buffer, Patch};
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

/** Computes the displacement from `from` to `to`. */
pub fn disp(from: usize, to: usize) -> i64 {
    if from > i64::MAX as usize || to > i64::MAX as usize {
        panic!("Displacements greater than isize::MAX are not supported");
    }
    (to as i64) - (from as i64)
}

/** Returns a bitmask representing `x` as a `bits`-bit unsigned integer. */
fn unsigned(x: u64, bits: usize) -> Option<u32> {
    let limit: u64 = 1 << bits;
    if x >= limit {
        None
    } else {
        Some((x & (limit - 1)) as u32)
    }
}

/** Returns a bitmask representing `x` as a `bits`-bit signed integer. */
fn signed(x: i64, bits: usize) -> Option<u32> {
    let limit: i64 = 1 << (bits - 1);
    if x >= limit || x < -limit {
        None
    } else {
        Some((x & (limit - 1)) as u32)
    }
}

//-----------------------------------------------------------------------------

/** The maximum allowable distance from a PC-relative load to its target. */
const PC_RELATIVE_RANGE: usize = 1 << 20;

/** An amount of free space that is probably large enough for a basic block. */
const COMFORTABLE_SPACE: usize = 1 << 12;

/**
 * An assembler, implementing a regularish subset of aarch64.
 */
pub struct Assembler<B: Buffer> {
    /**
     * The memory we're filling with code and immediate constants.
     *
     * We generate code forwards at `buffer.get_pos()`, and we collect
     * constants backwards at `self.pool_pos`. The interval between the two is
     * free space, as is everything beyond `pool_end`.
     */
    buffer: B,
    /** The write pointer for constants. Moves downwards. */
    pool_pos: usize,
    /** The end of the allocated memory. */
    pool_end: usize,
}

impl<B: Buffer> Assembler<B> {
    /** Construct an Assembler. */
    pub fn new() -> Self {
        let mut this = Assembler {buffer: B::new(), pool_pos: 0, pool_end: 0};
        this.alloc();
        this
    }

    /**
     * Abandons the free space between `buffer.get_pos()` and `self.pool_pos`,
     * and allocates a new interval of free space of size `PC_RELATIVE_RANGE`.
     */
    fn alloc(&mut self) {
        self.buffer.set_pos(self.pool_end);
        self.pool_end += PC_RELATIVE_RANGE;
        self.pool_pos = self.pool_end;
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

    /**
     * Returns the amount of free space between `buffer.get_pos()` and
     * `pool_pos`.
     */
    fn free_space(&self) -> usize {
        self.pool_pos - self.buffer.get_pos()
    }

    /**
     * Computes a bitmask representing the offset from [`get_pos()`] to
     * `target`. Returns a dummy value if the target is `None`. Returns `None`
     * if the target is not representable as a `bits`-bit signed integer.
     */
    fn jump_offset(&self, target: Option<usize>, bits: usize) -> Option<u32> {
        match target {
            Some(target) => signed(disp(self.get_pos(), target), bits),
            None => Some(1 << (bits - 1)),
        }
    }

    /**
     * Assembles an unconditional jump to `target`. Then, if the remaining free
     * space is smaller than `COMFORTABLE_SPACE`, call `alloc()`.
     */
    pub fn jump(&mut self, target: Option<usize>) -> Patch {
        let ret = Patch::new(self.get_pos());
        let offset = self.jump_offset(target, 28).expect("Cannot jump so far");
        assert_eq!(offset & 3, 0);
        let opcode = 0x14000000 | (offset >> 2);
        self.buffer.write(opcode as u64, 4);
        if self.free_space() < COMFORTABLE_SPACE {
            self.alloc();
        }
        ret
    }

    /**
     * If the remaining free space is smaller than 16 bytes, allocate a new
     * free space and assemble a jump to it.
     */
    fn check_space(&mut self) {
        if self.free_space() < 16 {
            let _patch = self.jump(Some(self.pool_end));
            assert_eq!(self.pool_pos - self.get_pos(), PC_RELATIVE_RANGE);
        }
    }

    /** Writes a 32-bit instruction, then calls `check_space()`. */
    fn write_instruction(&mut self, opcode: u32) {
        assert!(self.free_space() >= 8);
        self.buffer.write(opcode as u64, 4);
        self.check_space();
    }

    /** Writes an instruction which uses `rd` or `rt`. */
    fn write_d(&mut self, opcode: u32, rd: Register) {
        self.write_instruction(opcode | (rd as u32));
    }

    /** Writes a PC-relative load of a constant, then calls `check_space()`. */
    fn write_pc_relative(&mut self, rd: Register, imm: u64) {
        assert!(self.free_space() >= 16);
        // Write the constant.
        self.pool_pos -= 8;
        let pos = self.get_pos();
        self.set_pos(self.pool_pos);
        self.buffer.write(imm, 8);
        self.set_pos(pos);
        // Write the instruction.
        let offset = signed(disp(self.get_pos(), self.pool_pos), 19).unwrap();
        assert_eq!(offset & 3, 0);
        self.write_d(0x58000000 | ((offset >> 2) << 5), rd);
    }

    /** Writes an instruction to put an immediate constant in `rd`. */
    pub fn const_(&mut self, rd: Register, imm: u64) {
        // TODO: logic immediates.
        if let Some(imm) = unsigned(imm, 16) {
            // MOVZ.
            self.write_d(0xD2800000 | (imm << 5), rd);
        } else if let Some(imm) = unsigned(!imm, 16) {
            // MOVN.
            self.write_d(0x92800000 | (imm << 5), rd);
        } else if let Some(imm) = unsigned(0xFFFFFFFF & !imm, 16) {
            // 32-bit MOVN.
            self.write_d(0x12800000 | (imm << 5), rd);
        } else {
            self.write_pc_relative(rd, imm);
        }
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
