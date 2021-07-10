use super::{buffer, code, Patch, Shift, Unsigned, Register, RSP, Condition, MemOp, ShiftOp, AddOp, LogicOp};
use buffer::{Buffer};
use code::{Precision, Width};
use crate::util::{rotate_left};

use Precision::*;
use Register::*;

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
        Some((x & (2*limit - 1)) as u32)
    }
}

/**
 * Computes a bitmask representing the offset from [`get_pos()`] to
 * `target`. Returns a dummy value if the target is `None`. Returns `None`
 * if the offset is not encodable.
 */
pub fn jump_offset(from: usize, to: Option<usize>, bits: usize) -> Option<u32> {
    match to {
        Some(to) => {
            let offset = disp(from, to);
            assert_eq!(offset & 3, 0);
            signed(offset >> 2, bits)
        },
        None => {
            Some(1 << (bits - 1))
        },
    }
}

/**
 * Returns a bitmask representing `x` as a "logic immediate". The [encoding]
 * is quite esoteric. Here we use the ARM's terminology; see `DecodeBitMasks()`
 * in the [ARMv8 Architecture Reference Manual] (on page 7954).
 *
 * [encoding]: https://dinfuehr.github.io/blog/encoding-of-immediate-values-on-aarch64/
 * [ARMv8 Architecture Reference Manual]: https://documentation-service.arm.com/static/60119835773bb020e3de6fee
 */
#[allow(clippy::many_single_char_names)]
pub fn logic_immediate(prec: Precision, mut x: u64) -> Option<u32> {
    if prec == P32 {
        if (x >> 32) != 0 {
            panic!("High bits set in 32-bit immediate");
        }
        x |= x << 32;
    }
    // `0` and `-1` are not encodable.
    if x == 0 || x == !0 {
        return None;
    }
    // Count the first four runs of binary digits.
    let num_zeros = x.leading_zeros();
    x = rotate_left(x, num_zeros);
    let num_ones = (!x).leading_zeros();
    x = rotate_left(x, num_ones);
    let mut y = x;
    let num_zeros2 = y.leading_zeros();
    y = rotate_left(y, num_zeros2);
    let num_ones2 = (!y).leading_zeros();
    y = rotate_left(y, num_ones2);
    // `num_zeros2 + num_ones2` should be a whole repeating unit.
    if x != y {
        return None;
    }
    // The repeat length should be a power of two and not `1`.
    let esize = num_zeros2 + num_ones2;
    if !esize.is_power_of_two() || esize < 2 {
        return None;
    }
    // `num_zeros + num_ones` undid `ROR(welem, r)`.
    let r = num_zeros + num_ones;
    assert!(r <= esize);
    // `num_ones2` undid `Ones(s + 1)`.
    let s = num_ones2 - 1;
    assert!(s < esize);
    // Encode.
    let imms = (128 - 2 * esize + s) & 0x3F;
    let immr = r & (esize - 1);
    let n = (esize == 64) as u32;
    Some((n << 12) | (immr << 6) | imms)
}

//-----------------------------------------------------------------------------

/** The maximum allowable distance from a PC-relative load to its target. */
const PC_RELATIVE_RANGE: usize = 1 << 20;

/** An amount of free space that is probably large enough for a basic block. */
const COMFORTABLE_SPACE: usize = 1 << 12;

/**
 * An assembler, implementing a regularish subset of A64: the 64-bit subset of
 * AArch64.
 */
pub struct Assembler<B: Buffer> {
    /**
     * The memory we're filling with code and immediate constants.
     *
     * We generate code forwards at `self.pos`, and we collect constants
     * backwards at `self.pool_pos`. The interval between the two is
     * free space, as is everything beyond `pool_end`.
     */
    buffer: B,
    /** The write pointer for code. Moves upwards. */
    pos: usize,
    /** The write pointer for constants. Moves downwards. */
    pool_pos: usize,
    /** The end of the allocated memory. */
    pool_end: usize,
}

impl<B: Buffer> Assembler<B> {
    /** Constructs an Assembler. */
    pub fn new() -> Self {
        let mut this = Assembler {buffer: B::new(), pos: 0, pool_pos: 0, pool_end: 0};
        this.alloc();
        this
    }

    /**
     * Abandons the free space between `self.pos` and `self.pool_pos`,
     * and allocates a new interval of free space of size `PC_RELATIVE_RANGE`.
     */
    fn alloc(&mut self) {
        self.pos = self.pool_end;
        self.pool_end += PC_RELATIVE_RANGE;
        self.pool_pos = self.pool_end;
    }

    /** Applies `callback` to the contained [`Buffer`]. */
    pub fn use_buffer<T>(
        mut self,
        callback: impl FnOnce(B) -> std::io::Result<(B, T)>,
    ) -> std::io::Result<(Self, T)> {
        let (buffer, ret) = callback(self.buffer)?;
        self.buffer = buffer;
        Ok((self, ret))
    }

    /** Get the assembly pointer. */
    pub fn get_pos(&self) -> usize { self.pos }

    /** Set the assembly pointer. */
    pub fn set_pos(&mut self, pos: usize) { self.pos = pos; }

    /** Returns the amount of free space between `pos` and `pool_pos`. */
    fn free_space(&self) -> usize { self.pool_pos - self.pos }

    /**
     * Writes the last instruction of a basic block, and calls `alloc()` if
     * `free_space()` is low.
     */
    fn write_jump(&mut self, opcode: u32) {
        self.buffer.write(self.pos, opcode as u64, 4);
        self.pos += 4;
        if self.free_space() < COMFORTABLE_SPACE {
            self.alloc();
        }
    }

    /** Writes a jump instruction which uses `rn`. */
    fn write_jump_n(&mut self, mut opcode: u32, rn: Register) {
        opcode |= (rn as u32) << 5;
        self.write_jump(opcode);
    }

    /**
     * Writes a 32-bit instruction. Then, if the remaining free space is
     * smaller than 16 bytes, allocate a new free space and assemble a jump to
     * it.
     */
    fn write_instruction(&mut self, opcode: u32) {
        assert!(self.free_space() >= 8);
        self.buffer.write(self.pos, opcode as u64, 4);
        self.pos += 4;
        if self.free_space() < 16 {
            // Simplified `const_jump(self.pool_end)`.
            let offset = jump_offset(self.pos, Some(self.pool_end), 26).unwrap();
            self.write_jump(0x14000000 | offset);
            assert_eq!(self.free_space(), PC_RELATIVE_RANGE);
        }
    }

    /** Writes an instruction which uses `rd` or `rt`. */
    fn write_d(&mut self, mut opcode: u32, rd: Register) {
        opcode |= rd as u32;
        self.write_instruction(opcode);
    }

    /** Writes an instruction which uses `rn`. */
    fn write_n(&mut self, mut opcode: u32, rn: Register) {
        opcode |= (rn as u32) << 5;
        self.write_instruction(opcode);
    }

    /** Writes an instruction which uses `rd` or `rt`. */
    fn write_dn(&mut self, mut opcode: u32, rd: Register, rn: Register) {
        opcode |= rd as u32;
        opcode |= (rn as u32) << 5;
        self.write_instruction(opcode);
    }

    /** Writes an instruction which uses `rd` or `rt`. */
    fn write_dnm(&mut self, mut opcode: u32, rd: Register, rn: Register, rm: Register) {
        opcode |= rd as u32;
        opcode |= (rn as u32) << 5;
        opcode |= (rm as u32) << 16;
        self.write_instruction(opcode);
    }

    /** Writes an instruction which uses `Rt` and `Rt2`. */
    fn write_tt(&mut self, mut opcode: u32, rt: Register, rt2: Register) {
        opcode |= rt as u32;
        opcode |= (rt2 as u32) << 10;
        self.write_instruction(opcode);
    }    

    /** Writes a PC-relative load of a constant, then calls `check_space()`. */
    fn write_pc_relative(&mut self, rd: Register, imm: u64) {
        assert!(self.free_space() >= 16);
        // Write the constant.
        self.pool_pos -= 8;
        self.buffer.write(self.pool_pos, imm, 8);
        // Write the instruction.
        let offset = disp(self.pos, self.pool_pos);
        assert_eq!(offset & 3, 0);
        let offset = signed(offset >> 2, 19).unwrap();
        self.write_d(0x58000000 | (offset << 5), rd);
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
        } else if let Some(imm) = unsigned(0xFFFFFFFF ^ imm, 16) {
            // 32-bit MOVN.
            self.write_d(0x12800000 | (imm << 5), rd);
        } else {
            self.write_pc_relative(rd, imm);
        }
    }

    /**
     * Assembles a load or store instruction.
     *
     * The offset (`src.1`) can be a signed 9-bit number or `width` times an
     * unsigned 12-bit number. Other offsets are not encodable so this method
     * will panic.
     *
     * Some combinations of `op` and `width` make no sense, and this method
     * will panic in those cases.
     */
    pub fn mem(&mut self, op: MemOp, width: Width, data: Register, address: (Register, i64)) {
        if (op as usize) + (width as usize) > 5 {
            panic!("Too wide for LDRS");
        }
        let shift = width as usize;
        if let Some(imm) = unsigned((address.1 as u64) >> shift, 12) {
            if address.1 == ((imm as i64) << shift) {
                // Scaled unsigned.
                let mut opcode = 0x39000000;
                opcode |= imm << 10;
                opcode |= (op as u32) << 22;
                opcode |= (width as u32) << 30;
                self.write_dn(opcode, data, address.0);
                return;
            }
        }
        if let Some(imm) = signed(address.1, 9) {
            // Unscaled signed.
            let mut opcode = 0x38000000;
            opcode |= imm << 12;
            opcode |= (op as u32) << 22;
            opcode |= (width as u32) << 30;
            self.write_dn(opcode, data, address.0);
            return;
        }
        panic!("Cannot load so far");
    }

    /** Assembles an instruction that does `dest <- src1 <op> src2`. */
    pub fn shift(&mut self, op: ShiftOp, prec: Precision, dest: Register, src1: Register, src2: Register) {
        let mut opcode = 0x1AC02000;
        opcode |= (op as u32) << 10;
        opcode |= (prec as u32) << 31;
        self.write_dnm(opcode, dest, src1, src2);
    }

    /**
     * Assembles an instruction that does `dest <- src <op> constant`.
     * The [`Precision`] is taken from `shift`.
     */
    pub fn const_shift(&mut self, op: ShiftOp, dest: Register, src: Register, shift: Shift) {
        // Use an `ORR` instruction, with `RZR` as the unshifted source.
        // This is easier than ARM's choice of `BFM`, I think.
        let mut opcode = 0x0A000000 | (LogicOp::ORR as u32) << 29;
        opcode |= shift.amount() << 10;
        opcode |= (op as u32) << 22;
        opcode |= (shift.prec() as u32) << 31;
        self.write_dnm(opcode, dest, RZR, src);
    }

    /**
     * Assembles an instruction that does `dest <- src ± constant`. `dest` or `src`
     * can be `RSP` but not `RZR`.
     *  - prec - `P32` to zero-extend the result from 32 bits.
     *    flags.
     *  - constant - A 12-bit unsigned integer. This method will panic if the
     *    constant is not encodable.
     */
    pub fn const_add(&mut self, op: AddOp, prec: Precision, dest: Register, src: Register, constant: Unsigned<12>) {
        let mut opcode = 0x11000000;
        opcode |= constant.as_u32() << 10;
        opcode |= (op as u32) << 29;
        opcode |= (prec as u32) << 31;
        self.write_dn(opcode, dest, src);
    }

    /**
     * Assembles an instruction that does `dest <- src1 ± (src2 << shift)`.
     * `dest`, `src1` or `src2` can be `RZR` but not `RSP`.
     * The [`Precision`] is taken from `shift`.
     */
    pub fn shift_add(&mut self, op: AddOp, dest: Register, src1: Register, src2: Register, shift: Shift) {
        let mut opcode = 0x0B000000;
        opcode |= shift.amount() << 10;
        opcode |= (op as u32) << 29;
        opcode |= (shift.prec() as u32) << 31;
        self.write_dnm(opcode, dest, src1, src2);
    }

    /**
     * Assembles an instruction that does `dest <- src <op> constant`. `dest`
     * can be `RSP` but not `RZR`, except if `op` is `ANDS`, in which case it
     * can be `RZR` but not `RSP`. `src` can be `RZR` but not `RSP`.
     *  - prec - `P32` to zero-extend the result from 32 bits.
     *  - constant - A 12-bit unsigned integer, or the negative of one. This
     *    method will panic if the constant is not encodable.
     */
    pub fn const_logic(&mut self, op: LogicOp, prec: Precision, dest: Register, src: Register, constant: u64) {
        let mut opcode = 0x12000000;
        let imm = logic_immediate(prec, constant).expect("Invalid logic immediate");
        opcode |= imm << 10;
        opcode |= (op as u32) << 29;
        opcode |= (prec as u32) << 31;
        self.write_dn(opcode, dest, src);
    }

    /**
     * Assembles an instruction that does `dest <- src1 <op> (src2 << shift)`
     * or `dest <- src1 <op> not(src2 << shift)`. `dest`, `src1` or `src2` can
     * be `RZR` but not `RSP`.
     *  - not - `true` to invert the second operand (after shifting it).
     * The [`Precision`] is taken from `shift`.
     */
    pub fn shift_logic(&mut self, op: LogicOp, not: bool, dest: Register, src1: Register, src2: Register, shift: Shift) {
        let mut opcode = 0x0A000000;
        opcode |= shift.amount() << 10;
        opcode |= (not as u32) << 21;
        opcode |= (op as u32) << 29;
        opcode |= (shift.prec() as u32) << 31;
        self.write_dnm(opcode, dest, src1, src2);
    }

    /** Assembles an instruction that does `dest <- src1 * src2`. */
    pub fn mul(&mut self, prec: Precision, dest: Register, src1: Register, src2: Register) {
        let mut opcode = 0x1B000000 | (RZR as u32) << 10;
        opcode |= (prec as u32) << 31;
        self.write_dnm(opcode, dest, src1, src2);
    }

    /** Assembles an instruction that does `dest <- cond ? src1 : src2`. */
    pub fn csel(&mut self, prec: Precision, cond: Condition, dest: Register, src1: Register, src2: Register) {
        let mut opcode = 0x1A800000;
        opcode |= (cond as u32) << 12;
        opcode |= (prec as u32) << 31;
        self.write_dnm(opcode, dest, src1, src2);
    }

    /** Assembles a conditional jump to `target`. */
    pub fn jump_if(&mut self, cond: Condition, target: Option<usize>) -> Patch {
        let ret = Patch::new(self.get_pos());
        let mut opcode = 0x54800000;
        opcode |= cond as u32;
        self.write_instruction(opcode);
        self.patch(ret, None, target);
        ret
    }

    /** Assembles an indirect jump to `src`. */
    pub fn jump(&mut self, src: Register) {
        self.write_jump_n(0xD61F0000, src);
    }

    /** Assembles an unconditional jump to `target`. */
    pub fn const_jump(&mut self, target: Option<usize>) -> Patch {
        let ret = Patch::new(self.get_pos());
        self.write_jump(0x16000000);
        self.patch(ret, None, target);
        ret
    }

    /** Assembles an indirect call to `src`. */
    pub fn call(&mut self, src: Register) {
        self.write_n(0xD63F0000, src);
    }

    /** Assembles an unconditional jump to `target`. */
    pub fn const_call(&mut self, target: Option<usize>) -> Patch {
        let ret = Patch::new(self.get_pos());
        self.write_instruction(0x96000000);
        self.patch(ret, None, target);
        ret
    }

    /** Assembles a return to `src`. */
    pub fn ret(&mut self, src: Register) {
        self.write_jump_n(0xD65F0000, src);
    }

    /** Push `(src1, src2)`. */
    pub fn push(&mut self, src1: Register, src2: Register) {
        let opcode = 0xA9BF0000 | (RSP as u32) << 5;
        self.write_tt(opcode, src1, src2);
    }

    /** Pop `(src1, src2)`. */
    pub fn pop(&mut self, src1: Register, src2: Register) {
        let opcode = 0xA8C10000 | (RSP as u32) << 5;
        self.write_tt(opcode, src1, src2);
    }

    /**
     * Change the target of the instruction at `patch` from `old_target` to
     * `new_target`.
     * - patch - the instruction to modify.
     * - old_target - an offset from the beginning of the buffer, or `None`.
     * - new_target - an offset from the beginning of the buffer, or `None`.
     */
    pub fn patch(&mut self, patch: Patch, old_target: Option<usize>, new_target: Option<usize>) {
        let at = patch.address();
        let old = self.buffer.read(at, 4) as u32;
        let new = old ^ (
            if (old & 0xFF000010) == 0x54000000 {
                // Conditional branch.
                let old_offset = jump_offset(at, old_target, 19).unwrap();
                let new_offset = jump_offset(at, new_target, 19).expect("Cannot jump so far");
                assert_eq!(old & 0x00FFFFE0, old_offset << 5);
                (old_offset ^ new_offset) << 5
            } else if (old & 0x7C000000) == 0x14000000 {
                // Jump or call.
                let old_offset = jump_offset(at, old_target, 26).unwrap();
                let new_offset = jump_offset(at, new_target, 26).expect("Cannot jump so far");
                assert_eq!(old & 0x03FFFFFF, old_offset);
                old_offset ^ new_offset
            } else {
                panic!("not a jump or call instruction");
            }
        );
        self.buffer.write(at, new as u64, 4);
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
    use std::cmp::{min, max};

    use super::super::{ALL_CONDITIONS};
    use super::*;
    use MemOp::*;
    use Width::*;

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
        let mut a = Assembler::<Vec<u8>>::new();
        a.write_instruction(0x912AA3E0);
        a.write_instruction(0x9B007C00);
        disassemble(&a, 0, vec![
            "add x0, sp, #0xaa8",
            "mul x0, x0, x0",
        ]).unwrap();
    }

    #[test]
    fn mem() {
        let mut a = Assembler::<Vec<u8>>::new();
        for (rd, rn) in [(R0, RSP), (RZR, R0)] {
            for (op, width) in [
                (STR, One), (LDR, One), (LDRS64, One), (LDRS32, One),
                (STR, Two), (LDR, Two), (LDRS64, Two), (LDRS32, Two),
                (STR, Four), (LDR, Four), (LDRS64, Four),
                (STR, Eight), (LDR, Eight),
            ] {
                a.mem(op, width, rd, (rn, 4088));
                a.mem(op, width, rd, (rn, 255));
                a.mem(op, width, rd, (rn, -256));
            }
        }
        disassemble(&a, 0, vec![
            "strb w0, [sp, #0xff8]", "strb w0, [sp, #0xff]", "sturb w0, [sp, #0xffffffffffffff00]",
            "ldrb w0, [sp, #0xff8]", "ldrb w0, [sp, #0xff]", "ldurb w0, [sp, #0xffffffffffffff00]",
            "ldrsb x0, [sp, #0xff8]", "ldrsb x0, [sp, #0xff]", "ldursb x0, [sp, #0xffffffffffffff00]",
            "ldrsb w0, [sp, #0xff8]", "ldrsb w0, [sp, #0xff]", "ldursb w0, [sp, #0xffffffffffffff00]",
            "strh w0, [sp, #0xff8]", "sturh w0, [sp, #0xff]", "sturh w0, [sp, #0xffffffffffffff00]",
            "ldrh w0, [sp, #0xff8]", "ldurh w0, [sp, #0xff]", "ldurh w0, [sp, #0xffffffffffffff00]",
            "ldrsh x0, [sp, #0xff8]", "ldursh x0, [sp, #0xff]", "ldursh x0, [sp, #0xffffffffffffff00]",
            "ldrsh w0, [sp, #0xff8]", "ldursh w0, [sp, #0xff]", "ldursh w0, [sp, #0xffffffffffffff00]",
            "str w0, [sp, #0xff8]", "stur w0, [sp, #0xff]", "stur w0, [sp, #0xffffffffffffff00]",
            "ldr w0, [sp, #0xff8]", "ldur w0, [sp, #0xff]", "ldur w0, [sp, #0xffffffffffffff00]",
            "ldrsw x0, [sp, #0xff8]", "ldursw x0, [sp, #0xff]", "ldursw x0, [sp, #0xffffffffffffff00]",
            "str x0, [sp, #0xff8]", "stur x0, [sp, #0xff]", "stur x0, [sp, #0xffffffffffffff00]",
            "ldr x0, [sp, #0xff8]", "ldur x0, [sp, #0xff]", "ldur x0, [sp, #0xffffffffffffff00]",

            "strb wzr, [x0, #0xff8]", "strb wzr, [x0, #0xff]", "sturb wzr, [x0, #0xffffffffffffff00]",
            "ldrb wzr, [x0, #0xff8]", "ldrb wzr, [x0, #0xff]", "ldurb wzr, [x0, #0xffffffffffffff00]",
            "ldrsb xzr, [x0, #0xff8]", "ldrsb xzr, [x0, #0xff]", "ldursb xzr, [x0, #0xffffffffffffff00]",
            "ldrsb wzr, [x0, #0xff8]", "ldrsb wzr, [x0, #0xff]", "ldursb wzr, [x0, #0xffffffffffffff00]",
            "strh wzr, [x0, #0xff8]", "sturh wzr, [x0, #0xff]", "sturh wzr, [x0, #0xffffffffffffff00]",
            "ldrh wzr, [x0, #0xff8]", "ldurh wzr, [x0, #0xff]", "ldurh wzr, [x0, #0xffffffffffffff00]",
            "ldrsh xzr, [x0, #0xff8]", "ldursh xzr, [x0, #0xff]", "ldursh xzr, [x0, #0xffffffffffffff00]",
            "ldrsh wzr, [x0, #0xff8]", "ldursh wzr, [x0, #0xff]", "ldursh wzr, [x0, #0xffffffffffffff00]",
            "str wzr, [x0, #0xff8]", "stur wzr, [x0, #0xff]", "stur wzr, [x0, #0xffffffffffffff00]",
            "ldr wzr, [x0, #0xff8]", "ldur wzr, [x0, #0xff]", "ldur wzr, [x0, #0xffffffffffffff00]",
            "ldrsw xzr, [x0, #0xff8]", "ldursw xzr, [x0, #0xff]", "ldursw xzr, [x0, #0xffffffffffffff00]",
            "str xzr, [x0, #0xff8]", "stur xzr, [x0, #0xff]", "stur xzr, [x0, #0xffffffffffffff00]",
            "ldr xzr, [x0, #0xff8]", "ldur xzr, [x0, #0xff]", "ldur xzr, [x0, #0xffffffffffffff00]",
        ]).unwrap();
    }

    #[test]
    fn shift() {
        use ShiftOp::*;
        let mut a = Assembler::<Vec<u8>>::new();
        for prec in [P32, P64] {
            for op in [LSL, LSR, ASR, ROR] {
                for (rd, rn, rm) in [(R0, R1, RZR), (RZR, R0, R1), (R1, RZR, R0)] {
                    a.shift(op, prec, rd, rn, rm);
                }
                for (rd, rn) in [(R0, RZR), (RZR, R1)] {
                    a.const_shift(op, rd, rn, Shift::new(prec, 11).unwrap());
                }
            }
        }
        disassemble(&a, 0, vec![
            "lsl w0, w1, wzr", "lsl wzr, w0, w1", "lsl w1, wzr, w0",
            "orr w0, wzr, wzr, lsl #0xb", "orr wzr, wzr, w1, lsl #0xb",
            "lsr w0, w1, wzr", "lsr wzr, w0, w1", "lsr w1, wzr, w0",
            "orr w0, wzr, wzr, lsr #0xb", "orr wzr, wzr, w1, lsr #0xb",
            "asr w0, w1, wzr", "asr wzr, w0, w1", "asr w1, wzr, w0",
            "orr w0, wzr, wzr, asr #0xb", "orr wzr, wzr, w1, asr #0xb",
            "ror w0, w1, wzr", "ror wzr, w0, w1", "ror w1, wzr, w0",
            "orr w0, wzr, wzr, ror #0xb", "orr wzr, wzr, w1, ror #0xb",

            "lsl x0, x1, xzr", "lsl xzr, x0, x1", "lsl x1, xzr, x0",
            "orr x0, xzr, xzr, lsl #0xb", "orr xzr, xzr, x1, lsl #0xb",
            "lsr x0, x1, xzr", "lsr xzr, x0, x1", "lsr x1, xzr, x0",
            "orr x0, xzr, xzr, lsr #0xb", "orr xzr, xzr, x1, lsr #0xb",
            "asr x0, x1, xzr", "asr xzr, x0, x1", "asr x1, xzr, x0",
            "orr x0, xzr, xzr, asr #0xb", "orr xzr, xzr, x1, asr #0xb",
            "ror x0, x1, xzr", "ror xzr, x0, x1", "ror x1, xzr, x0",
            "orr x0, xzr, xzr, ror #0xb", "orr xzr, xzr, x1, ror #0xb",
        ]).unwrap();
    }

    #[test]
    fn add() {
        use AddOp::*;
        let mut a = Assembler::<Vec<u8>>::new();
        for prec in [P32, P64] {
            for op in [ADD, ADDS, SUB, SUBS] {
                for (rd, rn) in [(R0, RZR), (RZR, R0)] {
                    a.const_add(op, prec, rd, rn, Unsigned::new(4095).unwrap());
                    for rm in [R1, RZR] {
                        a.shift_add(op, rd, rn, rm, Shift::new(prec, 21).unwrap());
                    }
                }
            }
        }
        disassemble(&a, 0, vec![
            "add w0, wsp, #0xfff", "add w0, wzr, w1, lsl #0x15", "add w0, wzr, wzr, lsl #0x15",
            "add wsp, w0, #0xfff", "add wzr, w0, w1, lsl #0x15", "add wzr, w0, wzr, lsl #0x15",
            "adds w0, wsp, #0xfff", "adds w0, wzr, w1, lsl #0x15", "adds w0, wzr, wzr, lsl #0x15",
            "cmn w0, #0xfff", "cmn w0, w1, lsl #0x15", "cmn w0, wzr, lsl #0x15",
            "sub w0, wsp, #0xfff", "neg w0, w1, lsl #0x15", "neg w0, wzr, lsl #0x15",
            "sub wsp, w0, #0xfff", "sub wzr, w0, w1, lsl #0x15", "sub wzr, w0, wzr, lsl #0x15",
            "subs w0, wsp, #0xfff", "negs w0, w1, lsl #0x15", "negs w0, wzr, lsl #0x15",
            "cmp w0, #0xfff", "cmp w0, w1, lsl #0x15", "cmp w0, wzr, lsl #0x15",

            "add x0, sp, #0xfff", "add x0, xzr, x1, lsl #0x15", "add x0, xzr, xzr, lsl #0x15",
            "add sp, x0, #0xfff", "add xzr, x0, x1, lsl #0x15", "add xzr, x0, xzr, lsl #0x15",
            "adds x0, sp, #0xfff", "adds x0, xzr, x1, lsl #0x15", "adds x0, xzr, xzr, lsl #0x15",
            "cmn x0, #0xfff", "cmn x0, x1, lsl #0x15", "cmn x0, xzr, lsl #0x15",
            "sub x0, sp, #0xfff", "neg x0, x1, lsl #0x15", "neg x0, xzr, lsl #0x15",
            "sub sp, x0, #0xfff", "sub xzr, x0, x1, lsl #0x15", "sub xzr, x0, xzr, lsl #0x15",
            "subs x0, sp, #0xfff", "negs x0, x1, lsl #0x15", "negs x0, xzr, lsl #0x15",
            "cmp x0, #0xfff", "cmp x0, x1, lsl #0x15", "cmp x0, xzr, lsl #0x15"
        ]).unwrap();
    }

    #[test]
    fn logic_immediate() {
        // Exhaustively enumerate all encodable immediates.
        for prec in [P32, P64] {
            for (size, imms_size_bits, imms_length_mask) in [
                ( 2, 0b111100, 0b000001),
                ( 4, 0b111000, 0b000011),
                ( 8, 0b110000, 0b000111),
                (16, 0b100000, 0b001111),
                (32, 0b000000, 0b011111),
                (64, 0b000000, 0b111111),
            ] {
                if size == 64 && prec == P32 {
                    // There are no 32-bit constants with a size of 64.
                    continue;
                }
                for length in 0..imms_length_mask {
                    let pattern = (0..64).step_by(size as usize).fold(
                        (1 << (length + 1)) - 1,
                        |acc, shift| acc | (acc << shift));
                    for rotation in 0..size {
                        let mut val = crate::util::rotate_right(pattern, rotation);
                        if prec == P32 { val >>= 32 };
                        let n = (size == 64) as u32;
                        let immr = rotation;
                        let imms = imms_size_bits | length;
                        let encoding = (n << 12) | (immr << 6) | imms;
                        assert_eq!(
                            super::logic_immediate(prec, val),
                            Some(encoding),
                        );
                    }
                }
            }
        }
        // Check some notable non-encodable immediates.
        assert_eq!(super::logic_immediate(P32, 0x00000000), None);
        assert_eq!(super::logic_immediate(P32, 0xFFFFFFFF), None);
        assert_eq!(super::logic_immediate(P32, 0x5A5A5A5A), None);
        assert_eq!(super::logic_immediate(P32, 0x00000005), None);
        assert_eq!(super::logic_immediate(P64, 0x0000000000000000), None);
        assert_eq!(super::logic_immediate(P64, 0xFFFFFFFFFFFFFFFF), None);
        assert_eq!(super::logic_immediate(P64, 0x5A5A5A5A5A5A5A5A), None);
        assert_eq!(super::logic_immediate(P64, 0x0000000000000005), None);
    }

    #[test]
    fn logic() {
        use LogicOp::*;
        let mut a = Assembler::<Vec<u8>>::new();
        for (prec, value) in [(P32, 0x33333333), (P64, 0x3333333333333333)] {
            for op in [AND, ORR, EOR, ANDS] {
                for (rd, rn) in [(R0, RZR), (RZR, R0)] {
                    a.const_logic(op, prec, rd, rn, value);
                    for rm in [R1, RZR] {
                        a.shift_logic(op, false, rd, rn, rm, Shift::new(prec, 21).unwrap());
                        a.shift_logic(op, true, rd, rn, rm, Shift::new(prec, 11).unwrap());
                    }
                }
            }
        }
        disassemble(&a, 0, vec![
            "and w0, wzr, #0x33333333",
            "and w0, wzr, w1, lsl #0x15", "bic w0, wzr, w1, lsl #0xb",
            "and w0, wzr, wzr, lsl #0x15", "bic w0, wzr, wzr, lsl #0xb",
            "and wsp, w0, #0x33333333",
            "and wzr, w0, w1, lsl #0x15", "bic wzr, w0, w1, lsl #0xb",
            "and wzr, w0, wzr, lsl #0x15", "bic wzr, w0, wzr, lsl #0xb",
            "mov w0, #0x33333333",
            "orr w0, wzr, w1, lsl #0x15", "mvn w0, w1, lsl #0xb",
            "orr w0, wzr, wzr, lsl #0x15", "mvn w0, wzr, lsl #0xb",
            "orr wsp, w0, #0x33333333",
            "orr wzr, w0, w1, lsl #0x15", "orn wzr, w0, w1, lsl #0xb",
            "orr wzr, w0, wzr, lsl #0x15", "orn wzr, w0, wzr, lsl #0xb",
            "eor w0, wzr, #0x33333333",
            "eor w0, wzr, w1, lsl #0x15", "eon w0, wzr, w1, lsl #0xb",
            "eor w0, wzr, wzr, lsl #0x15", "eon w0, wzr, wzr, lsl #0xb",
            "eor wsp, w0, #0x33333333",
            "eor wzr, w0, w1, lsl #0x15", "eon wzr, w0, w1, lsl #0xb",
            "eor wzr, w0, wzr, lsl #0x15", "eon wzr, w0, wzr, lsl #0xb",
            "ands w0, wzr, #0x33333333",
            "ands w0, wzr, w1, lsl #0x15", "bics w0, wzr, w1, lsl #0xb",
            "ands w0, wzr, wzr, lsl #0x15", "bics w0, wzr, wzr, lsl #0xb",
            "tst w0, #0x33333333",
            "tst w0, w1, lsl #0x15", "bics wzr, w0, w1, lsl #0xb",
            "tst w0, wzr, lsl #0x15", "bics wzr, w0, wzr, lsl #0xb",

            "and x0, xzr, #0x3333333333333333",
            "and x0, xzr, x1, lsl #0x15", "bic x0, xzr, x1, lsl #0xb",
            "and x0, xzr, xzr, lsl #0x15", "bic x0, xzr, xzr, lsl #0xb",
            "and sp, x0, #0x3333333333333333",
            "and xzr, x0, x1, lsl #0x15", "bic xzr, x0, x1, lsl #0xb",
            "and xzr, x0, xzr, lsl #0x15", "bic xzr, x0, xzr, lsl #0xb",
            "orr x0, xzr, #0x3333333333333333", // Why not `mov`?
            "orr x0, xzr, x1, lsl #0x15", "mvn x0, x1, lsl #0xb",
            "orr x0, xzr, xzr, lsl #0x15", "mvn x0, xzr, lsl #0xb",
            "orr sp, x0, #0x3333333333333333",
            "orr xzr, x0, x1, lsl #0x15", "orn xzr, x0, x1, lsl #0xb",
            "orr xzr, x0, xzr, lsl #0x15", "orn xzr, x0, xzr, lsl #0xb",
            "eor x0, xzr, #0x3333333333333333",
            "eor x0, xzr, x1, lsl #0x15", "eon x0, xzr, x1, lsl #0xb",
            "eor x0, xzr, xzr, lsl #0x15", "eon x0, xzr, xzr, lsl #0xb",
            "eor sp, x0, #0x3333333333333333",
            "eor xzr, x0, x1, lsl #0x15", "eon xzr, x0, x1, lsl #0xb",
            "eor xzr, x0, xzr, lsl #0x15", "eon xzr, x0, xzr, lsl #0xb",
            "ands x0, xzr, #0x3333333333333333",
            "ands x0, xzr, x1, lsl #0x15", "bics x0, xzr, x1, lsl #0xb",
            "ands x0, xzr, xzr, lsl #0x15", "bics x0, xzr, xzr, lsl #0xb",
            "tst x0, #0x3333333333333333",
            "tst x0, x1, lsl #0x15", "bics xzr, x0, x1, lsl #0xb",
            "tst x0, xzr, lsl #0x15", "bics xzr, x0, xzr, lsl #0xb",
        ]).unwrap();
    }

    #[test]
    fn mul() {
        let mut a = Assembler::<Vec<u8>>::new();
        for prec in [P32, P64] {
            a.mul(prec, RZR, R0, R1);
            a.mul(prec, R0, R1, RZR);
            a.mul(prec, R1, RZR, R0);
        }
        disassemble(&a, 0, vec![
            "mul wzr, w0, w1",
            "mul w0, w1, wzr",
            "mul w1, wzr, w0",

            "mul xzr, x0, x1",
            "mul x0, x1, xzr",
            "mul x1, xzr, x0",
        ]).unwrap();
    }

    #[test]
    fn csel() {
        let mut a = Assembler::<Vec<u8>>::new();
        for prec in [P32, P64] {
            for cond in ALL_CONDITIONS {
                a.csel(prec, cond, RZR, R0, R1);
                a.csel(prec, cond, R0, R1, RZR);
                a.csel(prec, cond, R1, RZR, R0);
            }
        }
        disassemble(&a, 0, vec![
            "csel wzr, w0, w1, eq", "csel w0, w1, wzr, eq", "csel w1, wzr, w0, eq",
            "csel wzr, w0, w1, ne", "csel w0, w1, wzr, ne", "csel w1, wzr, w0, ne",
            "csel wzr, w0, w1, cs", "csel w0, w1, wzr, cs", "csel w1, wzr, w0, cs",
            "csel wzr, w0, w1, cc", "csel w0, w1, wzr, cc", "csel w1, wzr, w0, cc",
            "csel wzr, w0, w1, mi", "csel w0, w1, wzr, mi", "csel w1, wzr, w0, mi",
            "csel wzr, w0, w1, pl", "csel w0, w1, wzr, pl", "csel w1, wzr, w0, pl",
            "csel wzr, w0, w1, vs", "csel w0, w1, wzr, vs", "csel w1, wzr, w0, vs",
            "csel wzr, w0, w1, vc", "csel w0, w1, wzr, vc", "csel w1, wzr, w0, vc",
            "csel wzr, w0, w1, hi", "csel w0, w1, wzr, hi", "csel w1, wzr, w0, hi",
            "csel wzr, w0, w1, ls", "csel w0, w1, wzr, ls", "csel w1, wzr, w0, ls",
            "csel wzr, w0, w1, ge", "csel w0, w1, wzr, ge", "csel w1, wzr, w0, ge",
            "csel wzr, w0, w1, lt", "csel w0, w1, wzr, lt", "csel w1, wzr, w0, lt",
            "csel wzr, w0, w1, gt", "csel w0, w1, wzr, gt", "csel w1, wzr, w0, gt",
            "csel wzr, w0, w1, le", "csel w0, w1, wzr, le", "csel w1, wzr, w0, le",

            "csel xzr, x0, x1, eq", "csel x0, x1, xzr, eq", "csel x1, xzr, x0, eq",
            "csel xzr, x0, x1, ne", "csel x0, x1, xzr, ne", "csel x1, xzr, x0, ne",
            "csel xzr, x0, x1, cs", "csel x0, x1, xzr, cs", "csel x1, xzr, x0, cs",
            "csel xzr, x0, x1, cc", "csel x0, x1, xzr, cc", "csel x1, xzr, x0, cc",
            "csel xzr, x0, x1, mi", "csel x0, x1, xzr, mi", "csel x1, xzr, x0, mi",
            "csel xzr, x0, x1, pl", "csel x0, x1, xzr, pl", "csel x1, xzr, x0, pl",
            "csel xzr, x0, x1, vs", "csel x0, x1, xzr, vs", "csel x1, xzr, x0, vs", 
            "csel xzr, x0, x1, vc", "csel x0, x1, xzr, vc", "csel x1, xzr, x0, vc",
            "csel xzr, x0, x1, hi", "csel x0, x1, xzr, hi", "csel x1, xzr, x0, hi",
            "csel xzr, x0, x1, ls", "csel x0, x1, xzr, ls", "csel x1, xzr, x0, ls",
            "csel xzr, x0, x1, ge", "csel x0, x1, xzr, ge", "csel x1, xzr, x0, ge",
            "csel xzr, x0, x1, lt", "csel x0, x1, xzr, lt", "csel x1, xzr, x0, lt",
            "csel xzr, x0, x1, gt", "csel x0, x1, xzr, gt", "csel x1, xzr, x0, gt",
            "csel xzr, x0, x1, le", "csel x0, x1, xzr, le", "csel x1, xzr, x0, le",
        ]).unwrap();
    }

    #[test]
    fn jump() {
        let mut a = Assembler::<Vec<u8>>::new();
        let target = a.get_pos() + 28; // Somewhere in the middle of the code.
        a.const_jump(None);
        a.const_call(None);
        a.const_jump(Some(target));
        a.const_call(Some(target));
        for cond in ALL_CONDITIONS {
            a.jump_if(cond, Some(target));
        }
        a.const_jump(Some(target));
        a.const_call(Some(target));
        a.ret(RLR);
        disassemble(&a, 0, vec![
            "b 0xfffffffff8000000",
            "bl 0xfffffffff8000004",
            "b 0x1c",
            "bl 0x1c",
            "b.eq 0x1c",
            "b.ne 0x1c",
            "b.hs 0x1c",
            "b.lo 0x1c",
            "b.mi 0x1c",
            "b.pl 0x1c",
            "b.vs 0x1c",
            "b.vc 0x1c",
            "b.hi 0x1c",
            "b.ls 0x1c",
            "b.ge 0x1c",
            "b.lt 0x1c",
            "b.gt 0x1c",
            "b.le 0x1c",
            "b 0x1c",
            "bl 0x1c",
            "ret",
        ]).unwrap();
    }

    #[test]
    fn push_pop() {
        let mut a = Assembler::<Vec<u8>>::new();
        a.push(RZR, R0);
        a.pop(RZR, R0);
        a.push(R1, RZR);
        a.pop(R1, RZR);
        disassemble(&a, 0, vec![
            "stp xzr, x0, [sp, #0xfffffffffffffff0]!",
            "ldp xzr, x0, [sp], #0x10",
            "stp x1, xzr, [sp, #0xfffffffffffffff0]!",
            "ldp x1, xzr, [sp], #0x10",
        ]).unwrap();
    }

    #[test]
    fn patch() {
        let mut a = Assembler::<Vec<u8>>::new();
        let target = Some(4); // Somewhere in the middle of the code.
        let p1 = a.const_jump(None);
        let p2 = a.const_call(target);
        let p3 = a.jump_if(Condition::LS, target);
        disassemble(&a, 0, vec![
            "b 0xfffffffff8000000",
            "bl 0x4",
            "b.ls 0x4",
        ]).unwrap();
        let target2 = Some(0);
        a.patch(p1, None, target2);
        a.patch(p2, target, target2);
        a.patch(p3, target, None);
        disassemble(&a, 0, vec![
            "b 0x0",
            "bl 0x0",
            "b.ls 0xfffffffffff00008",
        ]).unwrap();
    }
}
