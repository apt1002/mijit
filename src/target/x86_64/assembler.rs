//! Tools for generating code using the x86_64 instruction set.
//!
//! The focus here is in concrete x86_64 instructions. One method call on an
//! Assembler generates one instruction. This ensures that documentation about
//! the x86_64 instructions set applies to the code we assemble. For example,
//! you can look up the costs of instructions.
//!
//! We make no attempt to be exhaustive. We implement a subset of x86_64 which
//! is sufficient for Mijit. Where we have freedom to do so, we choose to make
//! the subset as regular as possible, sometimes ignoring more efficient
//! encodings. We include unnecessary functionality (e.g. testing the P flag)
//! only if it is a regular generalization of functionality we need.

use super::super::{Label};
use super::{Buffer, CALLER_SAVES};

/**
 * All x86_64 registers that can be used interchangeably in our chosen subset
 * of x86_64. `SP` and `R12` cannot be used in the `rm` field of a ModR/M byte,
 * (assembled by `Assembler.load_op()`, for example), so they are excluded.
 *
 * All register names include a leading `R`, and omit a trailing `X`. This is
 * not intended to imply anything about the operand width, which is specified
 * in another way.
 */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
#[allow(clippy::upper_case_acronyms)]
pub enum Register {
    RA = 0,
    RC = 1,
    RD = 2,
    RB = 3,
    RSP = 4,
    RBP = 5,
    RSI = 6,
    RDI = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
}

use Register::*;

impl Register {
    /** Returns a bit pattern which includes `self` in all useful positions. */
    pub fn mask(self) -> u64 {
        [
            0x0000000000,
            0x0909090900, // 1
            0x1212121200, // 2
            0x1B1B1B1B00,
            0x2424242400, // 4
            0x2D2D2D2D00,
            0x3636363600,
            0x3F3F3F3F00,
            0x0000000007, // 8
            0x0909090907,
            0x1212121207,
            0x1B1B1B1B07,
            0x2424242407,
            0x2D2D2D2D07,
            0x3636363607,
            0x3F3F3F3F07,
        ][self as usize]
    }
}

//-----------------------------------------------------------------------------

/**
 * Represents the precision of an arithmetic operation.
 * With P32, the arithmetic is performed with 32-bit precision, and written
 * into the bottom 32 bits of the destination. The top 32 bits are 0.
 */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Precision {
    P32 = 0,
    P64 = 1,
}

use Precision::*;

impl Precision {
    pub fn bits(self) -> usize {
        match self {
            P32 => 32,
            P64 => 64,
        }
    }
    
    pub fn w_bit(self) -> u64 {
        (self as u64) << 3
    }
}

//-----------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum BinaryOp {
    Add = 0,
    Or = 1,
    Adc = 2,
    Sbb = 3,
    And = 4,
    Sub = 5,
    Xor = 6,
    Cmp = 7,
}

use BinaryOp::*;

impl BinaryOp {
    pub fn rm_imm(self, rm_is_reg: bool) -> u64 {
        0x808140 | (rm_is_reg as u64) << 22 | (self as u64) << 19
    }

    pub fn rm_reg(self, rm_is_reg: bool) -> u64 {
        0x800140 | (rm_is_reg as u64) << 22 | (self as u64) << 11
    }

    pub fn reg_rm(self, rm_is_reg: bool) -> u64 {
        0x800340 | (rm_is_reg as u64) << 22 | (self as u64) << 11
    }
}

//-----------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ShiftOp {
    Rol = 0,
    Ror = 1,
    Rcl = 2,
    Rcr = 3,
    Shl = 4,
    Shr = 5,
    // 6 is allegedly an undocumented synonym for 4.
    Sar = 7,
}

impl ShiftOp {
    pub fn rm_imm(self, rm_is_reg: bool) -> u64 {
        0x80C140 | (rm_is_reg as u64) << 22 | (self as u64) << 19
    }

    pub fn rm_c(self, rm_is_reg: bool) -> u64 {
        0x80D340 | (rm_is_reg as u64) << 22 | (self as u64) << 19
    }
}

//-----------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
#[allow(clippy::upper_case_acronyms)]
pub enum Condition {
    O  = 0x0,
    NO = 0x1,
    B  = 0x2,
    AE = 0x3,
    Z  = 0x4,
    NZ = 0x5,
    BE = 0x6,
    A  = 0x7,
    S  = 0x8,
    NS = 0x9,
    P  = 0xA,
    NP = 0xB,
    L  = 0xC,
    GE = 0xD,
    LE = 0xE,
    G  = 0xF,
}

impl Condition {
    pub fn move_if(self, is_true: bool) -> u64 {
        0xC0400F40 | ((!is_true as u64) ^ (self as u64)) << 16
    }

    pub fn load_if(self, is_true: bool) -> u64 {
        0x80400F40 | ((!is_true as u64) ^ (self as u64)) << 16
    }

    pub fn jump_if(self, is_true: bool) -> u64 {
        0x800F | ((!is_true as u64) ^ (self as u64)) << 8
    }
}

//-----------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Width {U8, S8, U16, S16, U32, S32, U64, S64}

use Width::*;

//-----------------------------------------------------------------------------

/** Computes the displacement from `from` to `to`. */
pub fn disp(from: usize, to: usize) -> isize {
    if from > isize::MAX as usize || to > isize::MAX as usize {
        panic!("Displacements greater than isize::MAX are not supported");
    }
    (to as isize) - (from as isize)
}

/** Computes the i32 displacement from `from` to `to`, if possible. */
pub fn disp32(from: usize, to: usize) -> i32 {
    let disp = disp(from, to);
    if disp > i32::MAX as isize || disp < i32::MIN as isize {
        panic!("The displacement does not fit in 32 bits");
    }
    disp as i32
}

/**
 * A value which, if used as the `rel32` part of a control-flow instruction,
 * is likely to result in an immediate crash.
 */
const UNKNOWN_DISP: i32 = -0x80000000;

/** Like [`disp32()`] but returns `UNKNOWN_DISP` if `to` is `None`. */
pub fn optional_disp32(from: usize, to: Option<usize>) -> i32 {
    to.map_or(UNKNOWN_DISP, |to| disp32(from, to))
}

#[no_mangle]
pub extern fn debug_word(x: u64) {
    println!("Debug: {:#018x}", x);
}

/**
 * An assembler, implementing a regularish subset of x86_64.
 *
 * You probably don't need to call the `write_x()` methods directly, but you
 * can if necessary (e.g. to assemble an instruction that is not provided by
 * Assembler itself). There is a `write_x()` method for each encoding pattern
 * `x`. Patterns are described [here](../doc/x86.rs). A typical pattern is
 * "ROOM" meaning a REX byte, two opcode bytes, and a ModR/M byte. There are
 * also `write_x()` methods for immediate constants, for displacements, and for
 * raw bytes.
 *
 * Instead, call the methods that assemble a single instruction. These include:
 *  - Variants of [`const_()`], [`load()`], and [`store()`], which assemble
 *  `MOV` instructions.
 *  - Variants of [`op()`], which assemble arithmetic instructions, including
 *  `CMP` instructions. For now, only 32-bit arithmetic operations are
 *  supported.
 *  - [`jump_if()`], [`ret()`], and variants of [`jump()`] and [`call()`],
 *  which assemble control-flow instructions.
 *  - [`push()`] and [`pop()`], which assemble `PUSH` and `POP` instructions.
 *
 * Registers are represented by type [`Register`]. Binary arithmetic operations
 * are represented by type [`BinaryOp`]. Condition codes are represented by
 * type [`Condition`].
 *
 * [`const_()`]: Assembler::const_
 * [`load()`]: Assembler::load
 * [`store()`]: Assembler::store
 * [`op()`]: Assembler::op
 * [`jump_if()`]: Assembler::jump_if
 * [`ret()`]: Assembler::ret
 * [`jump()`]: Assembler::jump
 * [`call()`]: Assembler::call
 * [`push()`]: Assembler::push
 * [`pop()`]: Assembler::pop
 */
pub struct Assembler<B: Buffer> {
    /// The area we're filling with code.
    buffer: B,
}

impl<B: Buffer> Assembler<B> {
    /** Construct an Assembler that writes to `buffer` */
    pub fn new(buffer: B) -> Self {
        Assembler {buffer: buffer}
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

    // Patterns and constants.

    /** Writes an 8-bit signed immediate constant. */
    pub fn write_imm8(&mut self, immediate: i8) {
        self.buffer.write(u64::from(immediate as u8), 1);
    }

    /** Writes a 32-bit signed immediate constant. */
    pub fn write_imm32(&mut self, immediate: i32) {
        self.buffer.write(u64::from(immediate as u32), 4);
    }

    /** Writes a 64-bit signed immediate constant. */
    pub fn write_imm64(&mut self, immediate: i64) {
        self.buffer.write(immediate as u64, 8);
    }

    /** Writes a 32-bit displacement from `self.get_pos()+4` to `target`. */
    pub fn write_rel32(&mut self, target: Option<usize>) {
        let pos = self.get_pos();
        self.write_imm32(optional_disp32(pos + 4, target));
    }

    /** Writes an instruction with pattern "OO", and no registers. */
    pub fn write_oo_0(&mut self, opcode: u64) {
        self.buffer.write(opcode, 2);
    }

    /** Writes an instruction with pattern "RO", and no registers. */
    pub fn write_ro_0(&mut self, opcode: u64) {
        self.buffer.write(opcode, 2);
    }

    /** Writes an instruction with pattern "RO", and one register. */
    pub fn write_ro_1(&mut self, mut opcode: u64, prec: Precision, rd: Register) {
        opcode |= prec.w_bit();
        opcode |= 0x0701 & rd.mask();
        self.buffer.write(opcode, 2);
    }

    /** Writes an instruction with pattern "ROM" and one register. */
    pub fn write_rom_1(&mut self, mut opcode: u64, prec: Precision, rm: Register) {
        opcode |= prec.w_bit();
        opcode |= 0x070001 & rm.mask();
        self.buffer.write(opcode, 3);
    }

    /** Writes an instruction with pattern "ROM" and two registers. */
    pub fn write_rom_2(&mut self, mut opcode: u64, prec: Precision, rm: Register, reg: Register) {
        opcode |= prec.w_bit();
        opcode |= 0x070001 & rm.mask();
        opcode |= 0x380004 & reg.mask();
        self.buffer.write(opcode, 3);
    }

    /** Writes an instruction with pattern "ROOM" and two registers. */
    pub fn write_room_2(&mut self, mut opcode: u64, prec: Precision, rm: Register, reg: Register) {
        opcode |= prec.w_bit();
        opcode |= 0x07000001 & rm.mask();
        opcode |= 0x38000004 & reg.mask();
        self.buffer.write(opcode, 4);
    }

    /**
     * If `rm` is `RSP` or `R12`, writes the byte `0x24`, otherwise does
     * nothing.
     *
     * This is necessary after a ModR/M byte if `rm` is used as a memory
     * operand, because the bit pattern 100 in the `rm` field indicates the
     * presence of a SIB byte. `0x24` is a SIB byte with 100 in the `index`
     * field, indicating no index, and 100 in the `base` field, matching `rm`.
     */
    pub fn write_sib_fix(&mut self, rm: Register) {
        if (rm as usize) & 7 == 4 {
            self.buffer.write_byte(0x24);
        }
    }

    // Instructions.

    /** Move register to register. */
    pub fn move_(&mut self, prec: Precision, dest: Register, src: Register) {
        self.write_rom_2(0xC08B40, prec, src, dest);
    }

    /** Move memory to register. */
    pub fn load(&mut self, prec: Precision, dest: Register, src: (Register, i32)) {
        self.write_rom_2(0x808B40, prec, src.0, dest);
        self.write_sib_fix(src.0);
        self.write_imm32(src.1);
    }

    /** Move register to memory. */
    pub fn store(&mut self, prec: Precision, dest: (Register, i32), src: Register) {
        self.write_rom_2(0x808940, prec, dest.0, src);
        self.write_sib_fix(dest.0);
        self.write_imm32(dest.1);
    }

    /**
     * Move constant to register.
     * If `imm` is zero, this will assemble the "zero idiom" xor instruction,
     * which corrupts the status flags. Use `const_preserving_flags` to avoid
     * this problem.
     */
    // TODO: Remove `prec`?
    pub fn const_(&mut self, prec: Precision, dest: Register, mut imm: i64) {
        if prec == P32 {
            imm &= 0xFFFFFFFF;
        }
        if imm == 0 {
            self.op(Xor, prec, dest, dest);
        } else {
            self.const_preserving_flags(prec, dest, imm);
        }
    }

    /**
     * Move constant to register.
     */
    pub fn const_preserving_flags(&mut self, prec: Precision, dest: Register, mut imm: i64) {
        if prec == P32 {
            imm &= 0xFFFFFFFF;
        }
        if i64::from(imm as u32) == imm {
            self.write_ro_1(0xB840, P32, dest);
            self.write_imm32(imm as i32);
        } else if i64::from(imm as i32) == imm {
            self.write_rom_1(0xC0C740, P64, dest);
            self.write_imm32(imm as i32);
        } else {
            self.write_ro_1(0xB840, P64, dest);
            self.write_imm64(imm);
        }
    }

    /** Op register to register. */
    pub fn op(&mut self, op: BinaryOp, prec: Precision, dest: Register, src: Register) {
        self.write_rom_2(op.rm_reg(true), prec, dest, src);
    }

    /** Op constant to register. */
    pub fn const_op(&mut self, op: BinaryOp, prec: Precision, dest: Register, imm: i32) {
        self.write_rom_1(op.rm_imm(true), prec, dest);
        self.write_imm32(imm);
    }

    /** Op a memory location to a register. */
    pub fn load_op(&mut self, op: BinaryOp, prec: Precision, dest: Register, src: (Register, i32)) {
        self.write_rom_2(op.reg_rm(false), prec, src.0, dest);
        self.write_sib_fix(src.0);
        self.write_imm32(src.1);
    }

    /** Shift register by `RC`. */
    pub fn shift(&mut self, op: ShiftOp, prec: Precision, dest: Register) {
        self.write_rom_1(op.rm_c(true), prec, dest);
    }

    /** Shift register by constant. */
    pub fn const_shift(&mut self, op: ShiftOp, prec: Precision, dest: Register, imm: u8) {
        assert!(imm < prec.bits() as u8);
        self.write_rom_1(op.rm_imm(true), prec, dest);
        self.write_imm8(imm as i8);
    }

    /** Multiply register by register. */
    pub fn mul(&mut self, prec: Precision, dest: Register, src: Register) {
        self.write_room_2(0xC0AF0F40, prec, src, dest);
    }

    /** Multiply register by constant. */
    pub fn const_mul(&mut self, prec: Precision, dest: Register, src: Register, imm: i32) {
        self.write_rom_2(0xC06940, prec, src, dest);
        self.write_imm32(imm);
    }

    /** Multiply register by memory. */
    pub fn load_mul(&mut self, prec: Precision, dest: Register, src: (Register, i32)) {
        self.write_room_2(0x80AF0F40, prec, src.0, dest);
        self.write_sib_fix(src.0);
        self.write_imm32(src.1);
    }

    /** Unsigned long divide (D, A) by register. Quotient in A, remainder in D. */
    pub fn udiv(&mut self, prec: Precision, src: Register) {
        self.write_rom_1(0xF0F740, prec, src);
    }

    /** Unsigned long divide (D, A) by memory. Quotient in A, remainder in D. */
    pub fn load_udiv(&mut self, prec: Precision, src: (Register, i32)) {
        self.write_rom_1(0xB0F740, prec, src.0);
        self.write_sib_fix(src.0);
        self.write_imm32(src.1);
    }

    /** Conditional move. */
    pub fn move_if(&mut self, cc: Condition, is_true: bool, prec: Precision, dest: Register, src: Register) {
        self.write_room_2(cc.move_if(is_true), prec, src, dest);
    }

    /** Conditional load. */
    pub fn load_if(&mut self, cc: Condition, is_true: bool, prec: Precision, dest: Register, src: (Register, i32)) {
        self.write_room_2(cc.load_if(is_true), prec, src.0, dest);
        self.write_sib_fix(src.0);
        self.write_imm32(src.1);
    }

    /** Conditional branch. */
    pub fn jump_if(&mut self, cc: Condition, is_true: bool, target: &mut Label) {
        let patch = self.get_pos();
        self.write_oo_0(cc.jump_if(is_true));
        self.write_imm32(UNKNOWN_DISP);
        self.lpush(target, patch);
    }

    /** Unconditional jump to a register. */
    pub fn jump(&mut self, target: Register) {
        self.write_rom_1(0xE0FF40, P32, target);
    }

    /** Unconditional jump to a constant. */
    pub fn const_jump(&mut self, target: &mut Label) {
        let patch = self.get_pos();
        self.write_ro_0(0xE940);
        self.write_imm32(UNKNOWN_DISP);
        self.lpush(target, patch);
    }

    /** Unconditional call to a register. */
    pub fn call(&mut self, target: Register) {
        self.write_rom_1(0xD0FF40, P32, target);
    }

    /** Unconditional call to a constant. */
    pub fn const_call(&mut self, target: &mut Label){
        let patch = self.get_pos();
        self.write_ro_0(0xE840);
        self.write_imm32(UNKNOWN_DISP);
        self.lpush(target, patch);
    }

    /**
     * Adds a control-flow instruction to `patches`, patching it to point to
     * this Label. Its previous target must be `DISP_UNKNOWN`.
     */
    fn lpush(&mut self, label: &mut Label, pos: usize) {
        self.patch(pos, label.target, None);
        label.push(pos)
    }

    /**
     * Change the target of the instruction at `pos` from `old_target` to
     * `new_target`.
     * - pos - the offset within the buffer of a jump or call instruction.
     * - new_target - an offset from the beginning of the buffer, or `None`.
     * - old_target - an offset from the beginning of the buffer, or `None`.
     */
    pub fn patch(&mut self, pos: usize, new_target: Option<usize>, old_target: Option<usize>) {
        let at = if self.buffer.read_byte(pos) == 0x0F && (self.buffer.read_byte(pos + 1) & 0xF0) == 0x80 {
            // jump_if
            pos + 2
        } else if self.buffer.read_byte(pos) == 0x40 && self.buffer.read_byte(pos + 1) == 0xE9 {
            // const_jump
            pos + 2
        } else if self.buffer.read_byte(pos) == 0x40 && self.buffer.read_byte(pos + 1) == 0xE8 {
            // const_call
            pos + 2
        } else {
            panic!("not a jump or call instruction");
        };
        let old_disp = self.buffer.read(at, 4) as i32;
        let old_pos = self.buffer.get_pos();
        self.buffer.set_pos(at);
        self.write_rel32(new_target);
        let at_plus_4 = self.buffer.get_pos();
        self.buffer.set_pos(old_pos);
        assert_eq!(old_disp, optional_disp32(at_plus_4, old_target));
    }

    pub fn ret(&mut self) {
        self.write_ro_0(0xC340);
    }

    /** Push a register. */
    pub fn push(&mut self, rd: Register) {
        self.write_ro_1(0x5040, P64, rd);
    }

    /** Pop a register. */
    pub fn pop(&mut self, rd: Register) {
        self.write_ro_1(0x5840, P64, rd);
    }

    /** Load narrow data, zero-extending to the given precision. */
    pub fn load_narrow(&mut self, prec: Precision, type_: Width, dest: Register, src: (Register, i32)) {
        match type_ {
            U8 => {
                self.write_room_2(0x80B60F40, prec, src.0, dest);
                self.write_sib_fix(src.0);
            }
            S8 => {
                self.write_room_2(0x80BE0F40, prec, src.0, dest);
                self.write_sib_fix(src.0);
            }
            U16 => {
                self.write_room_2(0x80B70F40, prec, src.0, dest);
                self.write_sib_fix(src.0);
            }
            S16 => {
                self.write_room_2(0x80BF0F40, prec, src.0, dest);
                self.write_sib_fix(src.0);
            }
            U32 => {
                self.write_rom_2(0x808B40, P32, src.0, dest);
                self.write_sib_fix(src.0);
            }
            S32 => {
                self.write_rom_2(0x806340, prec, src.0, dest);
                self.write_sib_fix(src.0);
            }
            U64 | S64 => {
                self.write_rom_2(0x808B40, prec, src.0, dest);
                self.write_sib_fix(src.0);
            }
        }
        self.write_imm32(src.1);
    }

    /** Store narrow data. */
    pub fn store_narrow(&mut self, type_: Width, dest: (Register, i32), src: Register) {
        match type_ {
            U8 | S8 => {
                self.write_rom_2(0x808840, P32, dest.0, src);
                self.write_sib_fix(dest.0);
            }
            U16 | S16 => {
                self.buffer.write_byte(0x66);
                self.write_rom_2(0x808940, P32, dest.0, src);
                self.write_sib_fix(dest.0);
            }
            U32 | S32 => {
                self.write_rom_2(0x808940, P32, dest.0, src);
                self.write_sib_fix(dest.0);
            }
            U64 | S64 => {
                self.write_rom_2(0x808940, P64, dest.0, src);
                self.write_sib_fix(dest.0);
            }
        }
        self.write_imm32(dest.1);
    }

    /** Call a function that prints `x` and can be used as a breakpoint. */
    pub fn debug(&mut self, x: Register) {
        if CALLER_SAVES.len() & 1 != 0 {
            // Adjust alignment of RSP is 16-byte aligned.
            self.push(CALLER_SAVES[0]);
        }
        for &r in &CALLER_SAVES {
            self.push(r);
        }
        self.move_(P64, RDI, x);
        self.const_(P64, RC, debug_word as *const() as i64);
        self.call(RC);
        for &r in CALLER_SAVES.iter().rev() {
            self.pop(r);
        }
        if CALLER_SAVES.len() & 1 != 0 {
            self.pop(CALLER_SAVES[0]);
        }
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;
    use ShiftOp::*;
    use Condition::*;

    use std::cmp::{max};

    use iced_x86::{Decoder, Formatter, NasmFormatter};

    use super::super::super::super::buffer::{VecU8, Mmap};

    const ALL_REGISTERS: [Register; 16] =
        [RA, RC, RD, RB, RSP, RBP, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15];
    const ALL_PRECISIONS: [Precision; 2] = [P32, P64];
    const ALL_BINARY_OPS: [BinaryOp; 8] =
        [Add, Or, Adc, Sbb, And, Sub, Xor, Cmp];
    const ALL_SHIFT_OPS: [ShiftOp; 7] =
        [Rol, Ror, Rcl, Rcr, Shl, Shr, Sar];
    const ALL_CONDITIONS: [Condition; 16] =
        [O, NO, B, AE, Z, NZ, BE, A, S, NS, P, NP, L, GE, LE, G];
    const ALL_WIDTHS: [Width; 8] =
        [U8, S8, U16, S16, U32, S32, U64, S64];

    fn new_assembler() -> Assembler<VecU8> {
        Assembler::new(VecU8::new(vec![0u8; 0x1000]))
    }

    /**
     * Disassemble the given x64_64 `code_bytes` as if they were at `code_ip`.
     */
    pub fn disassemble(code_bytes: &[u8], expected: Vec<&str>)
    -> Result<(), Vec<String>> {
        // Disassemble the code.
        let mut decoder = Decoder::new(64, code_bytes, 0);
        decoder.set_ip(0);
        let mut formatter = NasmFormatter::new();
        let mut ips = Vec::new();
        let mut byteses = Vec::new();
        let mut observed = Vec::new();
        for instruction in decoder {
            let start = instruction.ip() as usize;
            let len = instruction.len() as usize;
            ips.push(start);
            byteses.push(code_bytes[start..][..len].iter().rev().map(
                |b| format!("{:02X}", b)
            ).collect::<Vec<String>>().join(" "));
            let mut assembly = String::with_capacity(80);
            formatter.format(&instruction, &mut assembly);
            observed.push(assembly);
        };

        // Search for differences.
        let mut error = false;
        for i in 0..max(expected.len(), observed.len()) {
            let e_line = if i < expected.len() { &expected[i] } else { "missing" };
            let o_line = if i < observed.len() { &observed[i] } else { "missing" };
            if e_line != o_line {
                println!("Difference in line {}", i+1);
                println!("{:016X}   {:>32}   {}", ips[i], byteses[i], o_line);
                println!("{:>16}   {:>32}   {}", "Expected", "", e_line);
                error = true;
            }
        }
        if error { Err(observed) } else { Ok(()) }
    }

    #[test]
    fn add5() {
        let buffer = Mmap::new(0x1000).expect("Couldn't allocate");
        let mut a = Assembler::new(buffer);
        a.move_(P64, RA, RDI);
        a.const_op(Add, P64, RA, 5);
        a.ret();
        let (_, result) = a.use_buffer(|b| {
            b.execute(|bytes| {
                let f: extern "C" fn(i32) -> i32 = unsafe {std::mem::transmute(&bytes[0])};
                f(42)
            })
        }).expect("Couldn't change permissions");
        assert_eq!(result, 42 + 5);
    }

    #[test]
    fn test_disassemble() {
        let example_code = &[0x48, 0x89, 0x5C, 0x24, 0x10, 0x55];
        disassemble(example_code, vec![
            "mov [rsp+10h],rbx",
            "push rbp",
        ]).unwrap();
    }

    const IMM: i32 = 0x76543210;
    const DISP: i32 = 0x12345678;
    const LABEL: usize = 0x02461357;

    /** Test that the Registers are named correctly. */
    #[test]
    fn regs() {
        let mut a = new_assembler();
        for &r in &ALL_REGISTERS {
            a.move_(P32, r, r);
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "mov eax,eax",
            "mov ecx,ecx",
            "mov edx,edx",
            "mov ebx,ebx",
            "mov esp,esp",
            "mov ebp,ebp",
            "mov esi,esi",
            "mov edi,edi",
            "mov r8d,r8d",
            "mov r9d,r9d",
            "mov r10d,r10d",
            "mov r11d,r11d",
            "mov r12d,r12d",
            "mov r13d,r13d",
            "mov r14d,r14d",
            "mov r15d,r15d",
        ]).unwrap();
    }

    /** Test that the Precisions are named correctly. */
    #[test]
    fn precs() {
        let mut a = new_assembler();
        for &p in &ALL_PRECISIONS {
            a.move_(p, RA, RA);
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "mov eax,eax",
            "mov rax,rax",
        ]).unwrap();
    }

    /** Test that we can assemble all the different sizes of constant. */
    #[test]
    fn const_() {
        let mut a = new_assembler();
        for &p in &ALL_PRECISIONS {
            for &c in &[0, 1, 1000, 0x76543210, 0x76543210FEDCBA98] {
                a.const_(p, R8, c);
                a.const_(p, R15, !c);
            }
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "xor r8d,r8d",
            "mov r15d,0FFFFFFFFh",
            "mov r8d,1",
            "mov r15d,0FFFFFFFEh",
            "mov r8d,3E8h",
            "mov r15d,0FFFFFC17h",
            "mov r8d,76543210h",
            "mov r15d,89ABCDEFh",
            "mov r8d,0FEDCBA98h",
            "mov r15d,1234567h",
            "xor r8,r8",
            "mov r15,0FFFFFFFFFFFFFFFFh",
            "mov r8d,1",
            "mov r15,0FFFFFFFFFFFFFFFEh",
            "mov r8d,3E8h",
            "mov r15,0FFFFFFFFFFFFFC17h",
            "mov r8d,76543210h",
            "mov r15,0FFFFFFFF89ABCDEFh",
            "mov r8,76543210FEDCBA98h",
            "mov r15,89ABCDEF01234567h",
        ]).unwrap();
    }

    /** Test that we can assemble all the different kinds of "MOV". */
    #[test]
    fn move_() {
        let mut a = new_assembler();
        for &p in &ALL_PRECISIONS {
            a.move_(p, R10, R9);
            a.store(p, (R8, DISP), R10);
            a.store(p, (R12, DISP), R10);
            a.load(p, R11, (R8, DISP));
            a.load(p, R11, (R12, DISP));
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "mov r10d,r9d",
            "mov [r8+12345678h],r10d",
            "mov [r12+12345678h],r10d",
            "mov r11d,[r8+12345678h]",
            "mov r11d,[r12+12345678h]",
            "mov r10,r9",
            "mov [r8+12345678h],r10",
            "mov [r12+12345678h],r10",
            "mov r11,[r8+12345678h]",
            "mov r11,[r12+12345678h]",
        ]).unwrap();
    }

    /** Test that all the BinaryOps are named correctly. */
    #[test]
    fn binary_op() {
        let mut a = new_assembler();
        for &op in &ALL_BINARY_OPS {
            a.op(op, P32, R10, R9);
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "add r10d,r9d",
            "or r10d,r9d",
            "adc r10d,r9d",
            "sbb r10d,r9d",
            "and r10d,r9d",
            "sub r10d,r9d",
            "xor r10d,r9d",
            "cmp r10d,r9d",
        ]).unwrap();
    }

    /** Test that we can assemble BinaryOps in all the different ways. */
    #[test]
    fn binary_mode() {
        let mut a = new_assembler();
        for &p in &ALL_PRECISIONS {
            a.op(Add, p, R10, R9);
            a.const_op(Add, p, R10, IMM);
            a.load_op(Add, p, R9, (R8, DISP));
            a.load_op(Add, p, R9, (R12, DISP));
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "add r10d,r9d",
            "add r10d,76543210h",
            "add r9d,[r8+12345678h]",
            "add r9d,[r12+12345678h]",
            "add r10,r9",
            "add r10,76543210h",
            "add r9,[r8+12345678h]",
            "add r9,[r12+12345678h]",
        ]).unwrap();
    }

    /** Test that all the ShiftOps are named correctly. */
    #[test]
    fn shift_op() {
        let mut a = new_assembler();
        for &op in &ALL_SHIFT_OPS {
            a.shift(op, P32, R8);
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "rol r8d,cl",
            "ror r8d,cl",
            "rcl r8d,cl",
            "rcr r8d,cl",
            "shl r8d,cl",
            "shr r8d,cl",
            "sar r8d,cl",
        ]).unwrap();
    }

    /** Test that we can assemble ShiftOps in all the different ways. */
    #[test]
    fn shift_mode() {
        let mut a = new_assembler();
        for &p in &ALL_PRECISIONS {
            a.shift(Shl, p, R8);
            a.const_shift(Shl, p, R8, 7);
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "shl r8d,cl",
            "shl r8d,7",
            "shl r8,cl",
            "shl r8,7",
        ]).unwrap();
    }

    /** Test that we can assemble multiplications in all the different ways. */
    #[test]
    fn mul() {
        let mut a = new_assembler();
        for &p in &ALL_PRECISIONS {
            a.mul(p, R8, R9);
            a.const_mul(p, R10, R11, IMM);
            a.load_mul(p, R13, (R14, DISP));
            a.load_mul(p, R13, (R12, DISP));
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "imul r8d,r9d",
            "imul r10d,r11d,76543210h",
            "imul r13d,[r14+12345678h]",
            "imul r13d,[r12+12345678h]",
            "imul r8,r9",
            "imul r10,r11,76543210h",
            "imul r13,[r14+12345678h]",
            "imul r13,[r12+12345678h]",
        ]).unwrap();
    }

    /** Test that we can assemble divisions in all the different ways. */
    #[test]
    fn div() {
        let mut a = new_assembler();
        for &p in &ALL_PRECISIONS {
            a.udiv(p, R8);
            a.load_udiv(p, (R14, DISP));
            a.load_udiv(p, (R12, DISP));
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "div r8d",
            "div dword [r14+12345678h]",
            "div dword [r12+12345678h]",
            "div r8",
            "div qword [r14+12345678h]",
            "div qword [r12+12345678h]",
        ]).unwrap();
    }

    /**
     * Test that all the condition codes are named correctly.
     * Test that we can assemble conditional branches.
     */
    #[test]
    fn condition() {
        let mut a = new_assembler();
        let mut label = Label::new(Some(0x28)); // Somewhere in the middle of the code.
        for &cc in &ALL_CONDITIONS {
            a.jump_if(cc, true, &mut label);
            a.jump_if(cc, false, &mut label);
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "jo near 0000000000000028h",
            "jno near 0000000000000028h",
            "jno near 0000000000000028h",
            "jo near 0000000000000028h",
            "jb near 0000000000000028h",
            "jae near 0000000000000028h",
            "jae near 0000000000000028h",
            "jb near 0000000000000028h",
            "je near 0000000000000028h",
            "jne near 0000000000000028h",
            "jne near 0000000000000028h",
            "je near 0000000000000028h",
            "jbe near 0000000000000028h",
            "ja near 0000000000000028h",
            "ja near 0000000000000028h",
            "jbe near 0000000000000028h",
            "js near 0000000000000028h",
            "jns near 0000000000000028h",
            "jns near 0000000000000028h",
            "js near 0000000000000028h",
            "jp near 0000000000000028h",
            "jnp near 0000000000000028h",
            "jnp near 0000000000000028h",
            "jp near 0000000000000028h",
            "jl near 0000000000000028h",
            "jge near 0000000000000028h",
            "jge near 0000000000000028h",
            "jl near 0000000000000028h",
            "jle near 0000000000000028h",
            "jg near 0000000000000028h",
            "jg near 0000000000000028h",
            "jle near 0000000000000028h",
        ]).unwrap();
    }

    /** Test that we can assemble conditional moves and loads. */
    #[test]
    fn move_if() {
        let mut a = new_assembler();
        for &p in &ALL_PRECISIONS {
            a.move_if(G, true, p, R8, R9);
            a.move_if(G, false, p, R10, R11);
            a.load_if(G, true, p, RBP, (R13, DISP));
            a.load_if(G, false, p, R14, (R15, DISP));
            a.load_if(G, false, p, R14, (R12, DISP));
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "cmovg r8d,r9d",
            "cmovle r10d,r11d",
            "cmovg ebp,[r13+12345678h]",
            "cmovle r14d,[r15+12345678h]",
            "cmovle r14d,[r12+12345678h]",
            "cmovg r8,r9",
            "cmovle r10,r11",
            "cmovg rbp,[r13+12345678h]",
            "cmovle r14,[r15+12345678h]",
            "cmovle r14,[r12+12345678h]",
        ]).unwrap();
    }

    /** Test that we can assemble the different kinds of unconditional jump. */
    #[test]
    fn jump() {
        let mut a = new_assembler();
        let mut label = Label::new(Some(LABEL));
        a.jump(R8);
        a.const_jump(&mut label);
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "jmp r8",
            "jmp 0000000002461357h",
        ]).unwrap();
    }

    /** Test that we can assemble the different kinds of call and return. */
    #[test]
    fn call_ret() {
        let mut a = new_assembler();
        let mut label = Label::new(Some(LABEL));
        a.call(R8);
        a.const_call(&mut label);
        a.ret();
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "call r8",
            "call 0000000002461357h",
            "ret",
        ]).unwrap();
    }

    /** Test that we can assemble "PUSH" and "POP". */
    #[test]
    fn push_pop() {
        let mut a = new_assembler();
        a.push(R8);
        a.pop(R9);
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "push r8",
            "pop r9",
        ]).unwrap();
    }

    /** Test that we can assemble loads and stores for narrow data. */
    #[test]
    fn narrow() {
        let mut a = new_assembler();
        for &p in &ALL_PRECISIONS {
            for &w in &ALL_WIDTHS {
                a.load_narrow(p, w, R9, (R8, DISP));
                a.load_narrow(p, w, R9, (R12, DISP));
                a.store_narrow(w, (R8, DISP), R9);
                a.store_narrow(w, (R12, DISP), R9);
            }
        }
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "movzx r9d,byte [r8+12345678h]",
            "movzx r9d,byte [r12+12345678h]",
            "mov [r8+12345678h],r9b",
            "mov [r12+12345678h],r9b",
            "movsx r9d,byte [r8+12345678h]",
            "movsx r9d,byte [r12+12345678h]",
            "mov [r8+12345678h],r9b",
            "mov [r12+12345678h],r9b",
            "movzx r9d,word [r8+12345678h]",
            "movzx r9d,word [r12+12345678h]",
            "mov [r8+12345678h],r9w",
            "mov [r12+12345678h],r9w",
            "movsx r9d,word [r8+12345678h]",
            "movsx r9d,word [r12+12345678h]",
            "mov [r8+12345678h],r9w",
            "mov [r12+12345678h],r9w",
            "mov r9d,[r8+12345678h]",
            "mov r9d,[r12+12345678h]",
            "mov [r8+12345678h],r9d",
            "mov [r12+12345678h],r9d",
            "movsxd r9d,[r8+12345678h]",
            "movsxd r9d,[r12+12345678h]",
            "mov [r8+12345678h],r9d",
            "mov [r12+12345678h],r9d",
            "mov r9d,[r8+12345678h]",
            "mov r9d,[r12+12345678h]",
            "mov [r8+12345678h],r9",
            "mov [r12+12345678h],r9",
            "mov r9d,[r8+12345678h]",
            "mov r9d,[r12+12345678h]",
            "mov [r8+12345678h],r9",
            "mov [r12+12345678h],r9",
            
            "movzx r9,byte [r8+12345678h]",
            "movzx r9,byte [r12+12345678h]",
            "mov [r8+12345678h],r9b",
            "mov [r12+12345678h],r9b",
            "movsx r9,byte [r8+12345678h]",
            "movsx r9,byte [r12+12345678h]",
            "mov [r8+12345678h],r9b",
            "mov [r12+12345678h],r9b",
            "movzx r9,word [r8+12345678h]",
            "movzx r9,word [r12+12345678h]",
            "mov [r8+12345678h],r9w",
            "mov [r12+12345678h],r9w",
            "movsx r9,word [r8+12345678h]",
            "movsx r9,word [r12+12345678h]",
            "mov [r8+12345678h],r9w",
            "mov [r12+12345678h],r9w",
            "mov r9d,[r8+12345678h]",
            "mov r9d,[r12+12345678h]",
            "mov [r8+12345678h],r9d",
            "mov [r12+12345678h],r9d",
            "movsxd r9,[r8+12345678h]",
            "movsxd r9,[r12+12345678h]",
            "mov [r8+12345678h],r9d",
            "mov [r12+12345678h],r9d",
            "mov r9,[r8+12345678h]",
            "mov r9,[r12+12345678h]",
            "mov [r8+12345678h],r9",
            "mov [r12+12345678h],r9",
            "mov r9,[r8+12345678h]",
            "mov r9,[r12+12345678h]",
            "mov [r8+12345678h],r9",
            "mov [r12+12345678h],r9",
        ]).unwrap();
    }

    /** Test that we can patch jumps and calls. */
    #[test]
    fn patch() {
        let mut a = new_assembler();
        let mut label = Label::new(None);
        a.jump_if(Z, true, &mut label);
        a.const_jump(&mut label);
        a.const_call(&mut label);
        let len = a.get_pos();
        disassemble(&a.buffer[..len], vec![
            "je near 0FFFFFFFF80000006h",
            "jmp 0FFFFFFFF8000000Ch",
            "call 0FFFFFFFF80000012h",
        ]).unwrap();
        assert_eq!(label.patch(LABEL, |patch, old, new| a.patch(patch, old, new)).target(), None);
        disassemble(&a.buffer[..len], vec![
            "je near 0000000002461357h",
            "jmp 0000000002461357h",
            "call 0000000002461357h",
        ]).unwrap();
        assert_eq!(label.patch(LABEL, |patch, old, new| a.patch(patch, old, new)).target(), Some(LABEL));
        disassemble(&a.buffer[..len], vec![
            "je near 0000000002461357h",
            "jmp 0000000002461357h",
            "call 0000000002461357h",
        ]).unwrap();
    }

    /** Ensure the linker symbol `debug_word` is included in the binary. */
    #[test]
    fn not_really_a_test() {
        debug_word(0);
    }
}
