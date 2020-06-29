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
use std::mem;
use std::ops::{DerefMut};

//-----------------------------------------------------------------------------

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
pub enum Register {
    RA = 0,
    RD = 1,
    RC = 2,
    RB = 3,
    // SP is not a general-purpose register.
    RBP = 5,
    RSI = 6,
    RDI = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    // R12 is not a general-purpose register.
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

pub const ALL_REGISTERS: [Register; 14] =
    [RA, RD, RC, RB, RBP, RSI, RDI, R8, R9, R10, R11, R13, R14, R15];

//-----------------------------------------------------------------------------

/** Represents the value of the `scale` field of a `SIB` byte. */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Scale {
    One = 0,
    Two = 1,
    Four = 2,
    Eight = 3,
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

pub const ALL_BINARY_OPS: [BinaryOp; 8] =
    [Add, Or, Adc, Sbb, And, Sub, Xor, Cmp];

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
    // 6 is an undocumented synonym for 4.
    Sar = 7,
}

use ShiftOp::*;

impl ShiftOp {
    pub fn rm_imm(self, rm_is_reg: bool) -> u64 {
        0x80C140 | (rm_is_reg as u64) << 22 | (self as u64) << 19
    }

    pub fn rm_c(self, rm_is_reg: bool) -> u64 {
        0x80D340 | (rm_is_reg as u64) << 22 | (self as u64) << 19
    }
}

pub const ALL_SHIFT_OPS: [ShiftOp; 7] =
    [Rol, Ror, Rcl, Rcr, Shl, Shr, Sar];

//-----------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
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

use Condition::*;

impl Condition {
    pub fn jump_if(self, is_true: bool) -> u64 {
        0x800F | ((!is_true as u64) ^ (self as u64)) << 8
    }
}

pub const ALL_CONDITIONS: [Condition; 16] =
    [O, NO, B, AE, Z, NZ, BE, A, S, NS, P, NP, L, GE, LE, G];

//-----------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Width {U8, S8, U16, S16, U32, S32, U64, S64}

use Width::*;

pub const ALL_WIDTHS: [Width; 8] =
    [U8, S8, U16, S16, U32, S32, U64, S64];

//-----------------------------------------------------------------------------

/**
 * Represents a control-flow instruction whose target can be mutated with
 * `Assembler.patch()`.
 */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Patch {
    JumpIf(usize),
    ConstJump(usize),
    ConstCall(usize),
}

//-----------------------------------------------------------------------------

pub fn disp(from: usize, to: usize) -> isize {
    if from > isize::MAX as usize || to > isize::MAX as usize {
        panic!("Displacements greater than isize::MAX are not supported");
    }
    (to as isize) - (from as isize)
}

pub fn disp32(from: usize, to: usize) -> i32 {
    let disp = disp(from, to);
    if disp > i32::MAX as isize || disp < i32::MIN as isize {
        panic!("The displacement does not fit in 32 bits");
    }
    disp as i32
}

pub fn add_disp(from: usize, disp: isize) -> usize {
    if from > isize::MAX as usize {
        panic!("Labels greater than isize::MAX are not supported");
    }
    (from as isize).checked_add(disp)
        .expect("Labels greater than isize::MAX are not supported")
        as usize
}

/**
 * An assembler, implementing a regularish subset of x86_64.
 *
 * The low-level memory address of `buffer` definitely won't change while the
 * Assembler exists, but it could change at other times, e.g. because the
 * containing Vec grows and gets reallocated. Therefore, be wary of absolute
 * memory addresses. Assembler itself never uses them, and instead represents
 * addresses as displacements from the beginning of `buffer`.
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
 *  - Variants of [`const()`], [`load()`], and [`store()`], which assemble
 *  `MOV` instructions.
 *  - Variants of `op()`, which assemble arithmetic instructions, including
 *  `CMP` instructions. For now, only 32-bit arithmetic operations are
 *  supported.
 *  - `jump_if()`, `ret()`, and variants of `jump()` and `call()`, which
 *  assemble control-flow instructions.
 *  - `push()` and `pop()`, which assemble `PUSH` and `POP` instructions.
 *
 * Registers are represented by type [`Register`]. Binary arithmetic operations
 * are represented by type [`BinaryOp`]. Condition codes are represented by
 * type [`Condition`].
 *
 * To generate a jump or call to an as-yet unknown constant destination, use
 * `None` as the target, and fill in the returned `Patch` later.
 */
pub struct Assembler<'a> {
    /// The area we're filling with code.
    pub buffer: &'a mut [u8],
    /// The assembly pointer: an index into `buffer`.
    pub pos: usize,
}

impl<'a> Assembler<'a> {
    /** Construct an Assembler that writes to `buffer` */
    pub fn new<T: DerefMut<Target=[u8]>>(buffer: &'a mut T) -> Self {
        Assembler {buffer: &mut *buffer, pos: 0}
    }

    /** Returns current assembly pointer. */
    pub fn label(&self) -> usize {
        self.pos
    }

    /** Set the assembly pointer. */
    pub fn goto(&mut self, pos: usize) {
        self.pos = pos;
    }

    /** Reads a single byte. */
    pub fn read_byte(&self, pos: usize) -> u8 {
        self.buffer[pos]
    }

    /** Writes a single byte at the assembly pointer, incrementing it. */
    pub fn write_byte(&mut self, byte: u8) {
        self.buffer[self.pos] = byte;
        self.pos += 1;
    }

    /**
     * Reads up to 8 bytes, as if using `read_byte()` repeatedly.
     */
    pub fn read(&self, pos: usize, len: usize) -> u64 {
        assert!(len <= 8);
        let mut bytes: u64 = 0;
        for i in (0..len).rev() {
            bytes <<= 8;
            bytes |= self.read_byte(pos + i) as u64;
        }
        bytes
    }

    /**
     * Writes up to 8 bytes at the assembly pointer, as if using
     * `write_byte()` repeatedly.
     */
    pub fn write(&mut self, mut bytes: u64, len: usize) {
        assert!(len <= 8);
        for _ in 0..len {
            self.write_byte(bytes as u8);
            bytes >>= 8;
        }
        assert_eq!(bytes, 0);
    }

    // Patterns and constants.

    /** Writes an 8-bit signed immediate constant. */
    pub fn write_imm8(&mut self, immediate: i8) {
        self.write((immediate as u8) as u64, 1);
    }

    /** Writes a 32-bit signed immediate constant. */
    pub fn write_imm32(&mut self, immediate: i32) {
        self.write((immediate as u32) as u64, 4);
    }

    /** Writes a 32-bit displacement from `pos+4` to `target`. */
    pub fn write_rel32(&mut self, target: Option<usize>) {
        let disp = if let Some(target) = target {
            disp32(self.pos + 4, target)
        } else {
            -0x80000000
        };
        self.write_imm32(disp);
    }

    /** Writes an instruction with pattern "OO", and no registers. */
    pub fn write_oo_0(&mut self, opcode: u64) {
        self.write(opcode, 2);
    }

    /** Writes an instruction with pattern "RO", and no registers. */
    pub fn write_ro_0(&mut self, opcode: u64) {
        self.write(opcode, 2);
    }

    /** Writes an instruction with pattern "RO", and one register. */
    pub fn write_ro_1(&mut self, mut opcode: u64, rd: Register) {
        opcode |= 0x0701 & rd.mask();
        self.write(opcode, 2);
    }

    /** Writes an instruction with pattern "ROM" and one register. */
    pub fn write_rom_1(&mut self, mut opcode: u64, rm: Register) {
        opcode |= 0x070001 & rm.mask();
        self.write(opcode, 3);
    }

    /** Writes an instruction with pattern "ROM" and two registers. */
    pub fn write_rom_2(&mut self, mut opcode: u64, rm: Register, reg: Register) {
        opcode |= 0x070001 & rm.mask();
        opcode |= 0x380004 & reg.mask();
        self.write(opcode, 3);
    }

    /** Writes an instruction with pattern "ROOM" and two registers. */
    pub fn write_room_2(&mut self, mut opcode: u64, rm: Register, reg: Register) {
        opcode |= 0x07000001 & rm.mask();
        opcode |= 0x38000004 & reg.mask();
        self.write(opcode, 4);
    }

    // Instructions.

    /** Move register to register. */
    pub fn mov(&mut self, dest: Register, src: Register) {
        self.write_rom_2(0xC08B40, src, dest);
    }

    /** Move memory to register. */
    pub fn load(&mut self, dest: Register, src: (Register, i32)) {
        self.write_rom_2(0x808B40, src.0, dest);
        self.write_imm32(src.1);
    }

    /** Move register to memory. */
    pub fn store(&mut self, dest: (Register, i32), src: Register) {
        self.write_rom_2(0x808940, dest.0, src);
        self.write_imm32(dest.1);
    }

    /** Move constant to register. */
    pub fn const_(&mut self, dest: Register, imm: i32) {
        self.write_ro_1(0xB840, dest);
        self.write_imm32(imm);
    }

    /** Op register to register. */
    pub fn op(&mut self, op: BinaryOp, dest: Register, src: Register) {
        self.write_rom_2(op.rm_reg(true), dest, src);
    }

    /** Op constant to register. */
    pub fn const_op(&mut self, op: BinaryOp, dest: Register, imm: i32) {
        self.write_rom_1(op.rm_imm(true), dest);
        self.write_imm32(imm);
    }

    /** Op a memory location to a register. */
    pub fn load_op(&mut self, op: BinaryOp, dest: Register, src: (Register, i32)) {
        self.write_rom_2(op.reg_rm(false), src.0, dest);
        self.write_imm32(src.1);
    }

    /** Shift register by `RC`. */
    pub fn shift(&mut self, op: ShiftOp, dest: Register) {
        self.write_rom_1(op.rm_c(true), dest);
    }

    /** Shift register by constant. */
    pub fn const_shift(&mut self, op: ShiftOp, dest: Register, imm: u8) {
        assert!(imm < 32);
        self.write_rom_1(op.rm_imm(true), dest);
        self.write_imm8(imm as i8);
    }

    /** Conditional branch. */
    pub fn jump_if(&mut self, cc: Condition, is_true: bool, target: Option<usize>) -> Patch {
        let label = self.label();
        self.write_oo_0(cc.jump_if(is_true));
        self.write_rel32(target);
        Patch::JumpIf(label)
    }

    /** Unconditional jump to a register. */
    pub fn jump(&mut self, target: Register) {
        self.write_rom_1(0xE0FF40, target);
    }

    /** Unconditional jump to a constant. */
    pub fn const_jump(&mut self, target: Option<usize>) -> Patch {
        let label = self.label();
        self.write_ro_0(0xE940);
        self.write_rel32(target);
        Patch::ConstJump(label)
    }

    /** Unconditional call to a register. */
    pub fn call(&mut self, target: Register) {
        self.write_rom_1(0xD0FF40, target);
    }

    /** Unconditional call to a constant. */
    pub fn const_call(&mut self, target: Option<usize>) -> Patch {
        let label = self.label();
        self.write_ro_0(0xE840);
        self.write_rel32(target);
        Patch::ConstCall(label)
    }

    pub fn patch(&mut self, patch: Patch, target: usize) -> Option<usize> {
        let mut at = match patch {
            Patch::JumpIf(addr) => {
                assert_eq!(self.buffer[addr], 0x0F);
                assert_eq!(self.buffer[addr + 1] & 0xF0, 0x80);
                addr + 2
            },
            Patch::ConstJump(addr) => {
                assert_eq!(self.buffer[addr], 0x40,);
                assert_eq!(self.buffer[addr + 1], 0xE9);
                addr + 2
            },
            Patch::ConstCall(addr) => {
                assert_eq!(self.buffer[addr], 0x40);
                assert_eq!(self.buffer[addr + 1], 0xE8);
                addr + 2
            },
        };
        let old_disp = self.read(at, 4);
        mem::swap(&mut at, &mut self.pos);
        self.write_rel32(Some(target));
        mem::swap(&mut at, &mut self.pos);
        if old_disp == 0x80000000 {
            None
        } else {
            Some(add_disp(at, old_disp as i32 as isize))
        }
    }

    pub fn ret(&mut self) {
        self.write_ro_0(0xC340);
    }

    /** Push a register. */
    pub fn push(&mut self, rd: Register) {
        self.write_ro_1(0x5040, rd);
    }

    /** Pop a register. */
    pub fn pop(&mut self, rd: Register) {
        self.write_ro_1(0x5840, rd);
    }

    /** Store narrow data. */
    pub fn store_narrow(&mut self, type_: Width, dest: (Register, i32), src: Register) {
        match type_ {
            U8 | S8 => {
                self.write_rom_2(0x808840, dest.0, src);
            }
            U16 | S16 => {
                self.write_byte(0x66);
                self.write_rom_2(0x808940, dest.0, src);
            }
            U32 | S32 => {
                self.write_rom_2(0x808940, dest.0, src);
            }
            U64 | S64 => {
                self.write_rom_2(0x808948, dest.0, src);
            }
        }
        self.write_imm32(dest.1);
    }

    /** Load narrow data, zero-extending to 64 bits. */
    pub fn load_narrow(&mut self, type_: Width, dest: Register, src: (Register, i32)) {
        match type_ {
            U8 => {
                self.write_room_2(0x80B60F48, src.0, dest);
            }
            S8 => {
                self.write_room_2(0x80BE0F48, src.0, dest);
            }
            U16 => {
                self.write_room_2(0x80B70F48, src.0, dest);
            }
            S16 => {
                self.write_room_2(0x80BF0F48, src.0, dest);
            }
            U32 => {
                self.write_rom_2(0x808B40, src.0, dest);
            }
            S32 => {
                self.write_rom_2(0x806348, src.0, dest);
            }
            U64 | S64 => {
                self.write_rom_2(0x808B48, src.0, dest);
            }
        }
        self.write_imm32(src.1);
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use std::cmp::{max};

    use iced_x86::{Decoder, Formatter, NasmFormatter};

    pub struct DisassemblyError {
        observed: Vec<String>,
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
                println!("{:016X}   {:>32}   {:}", ips[i], byteses[i], o_line);
                println!("Expected {}", e_line);
                error = true;
            }
        }
        if error { Err(observed) } else { Ok(()) }
    }

    #[test]
    fn test_disassemble() {
        let example_code = &[0x48, 0x89, 0x5C, 0x24, 0x10, 0x55];
        disassemble(example_code, vec![
            "mov [rsp+10h],rbx",
            "push rbp",
        ]).unwrap();
    }

    use super::*;

    const IMM: i32 = 0x76543210;
    const DISP: i32 = 0x12345678;
    const LABEL: usize = 0x02461357;

    /** Test that the Registers are named correctly. */
    #[test]
    fn regs() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        for &r in &ALL_REGISTERS {
            a.mov(r, r);
        }
        let len = a.label();
        disassemble(&code_bytes[..len], vec![
            "mov eax,eax",
            "mov ecx,ecx",
            "mov edx,edx",
            "mov ebx,ebx",
            "mov ebp,ebp",
            "mov esi,esi",
            "mov edi,edi",
            "mov r8d,r8d",
            "mov r9d,r9d",
            "mov r10d,r10d",
            "mov r11d,r11d",
            "mov r13d,r13d",
            "mov r14d,r14d",
            "mov r15d,r15d",
        ]).unwrap();
    }

    /** Test that we can assemble all the different kinds of "MOV". */
    #[test]
    fn mov() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        a.const_(R9, IMM);
        a.mov(R10, R9);
        a.store((R8, DISP), R10);
        a.load(R11, (R8, DISP));
        let len = a.label();
        disassemble(&code_bytes[..len], vec![
            "mov r9d,76543210h",
            "mov r10d,r9d",
            "mov [r8+12345678h],r10d",
            "mov r11d,[r8+12345678h]",
        ]).unwrap();
    }

    /** Test that all the BinaryOps are named correctly. */
    #[test]
    fn binary_op() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        for &op in &ALL_BINARY_OPS {
            a.op(op, R10, R9);
        }
        let len = a.label();
        disassemble(&code_bytes[..len], vec![
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
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        a.op(Add, R10, R9);
        a.const_op(Add, R10, IMM);
        a.load_op(Add, R9, (R8, DISP));
        let len = a.label();
        disassemble(&code_bytes[..len], vec![
            "add r10d,r9d",
            "add r10d,76543210h",
            "add r9d,[r8+12345678h]",
        ]).unwrap();
    }

    /** Test that all the ShiftOps are named correctly. */
    #[test]
    fn shift_op() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        for &op in &ALL_SHIFT_OPS {
            a.shift(op, R8);
        }
        let len = a.label();
        disassemble(&code_bytes[..len], vec![
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
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        a.shift(Shl, R8);
        a.const_shift(Shl, R8, 7);
        let len = a.label();
        disassemble(&code_bytes[..len], vec![
            "shl r8d,cl",
            "shl r8d,7",
        ]).unwrap();
    }

    /**
     * Test that all the condition codes are named correctly.
     * Test that we can assemble conditional branches.
     */
    #[test]
    fn condition() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        let target: usize = 0x28; // Somewhere in the middle of the code.
        for &cc in &ALL_CONDITIONS {
            a.jump_if(cc, true, Some(target));
            a.jump_if(cc, false, Some(target));
        }
        let len = a.label();
        disassemble(&code_bytes[..len], vec![
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

    /** Test that we can assemble the different kinds of unconditional jump. */
    #[test]
    fn jump() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        a.jump(R8);
        a.const_jump(Some(LABEL));
        let len = a.label();
        disassemble(&code_bytes[..len], vec![
            "jmp r8",
            "jmp 0000000002461357h",
        ]).unwrap();
    }

    /** Test that we can assemble the different kinds of call and return. */
    #[test]
    fn call_ret() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        a.call(R8);
        a.const_call(Some(LABEL));
        a.ret();
        let len = a.label();
        disassemble(&code_bytes[..len], vec![
            "call r8",
            "call 0000000002461357h",
            "ret",
        ]).unwrap();
    }

    /** Test that we can assemble "PUSH" and "POP". */
    #[test]
    fn push_pop() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        a.push(R8);
        a.pop(R9);
        let len = a.label();
        disassemble(&code_bytes[..len], vec![
            "push r8",
            "pop r9",
        ]).unwrap();
    }

    /** Test that we can assmeble loads and stores for narrow data. */
    #[test]
    fn narrow() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        for &w in &ALL_WIDTHS {
            a.load_narrow(w, R9, (R8, DISP));
            a.store_narrow(w, (R8, DISP), R9);
        }
        let len = a.label();
        disassemble(&code_bytes[..len], vec![
            "movzx r9,byte [r8+12345678h]",
            "mov [r8+12345678h],r9b",
            "movsx r9,byte [r8+12345678h]",
            "mov [r8+12345678h],r9b",
            "movzx r9,word [r8+12345678h]",
            "mov [r8+12345678h],r9w",
            "movsx r9,word [r8+12345678h]",
            "mov [r8+12345678h],r9w",
            "mov r9d,[r8+12345678h]",
            "mov [r8+12345678h],r9d",
            "movsxd r9,dword [r8+12345678h]",
            "mov [r8+12345678h],r9d",
            "mov r9,[r8+12345678h]",
            "mov [r8+12345678h],r9",
            "mov r9,[r8+12345678h]",
            "mov [r8+12345678h],r9",
        ]).unwrap();
    }

    /** Test that we can patch jumps and calls. */
    #[test]
    fn patch() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        let p1 = a.jump_if(Z, true, None);
        let p2 = a.const_jump(None);
        let p3 = a.const_call(None);
        let len = a.label();
        disassemble(&code_bytes[..len], vec![
            "je near 0FFFFFFFF80000006h",
            "jmp 0FFFFFFFF8000000Ch",
            "call 0FFFFFFFF80000012h",
        ]).unwrap();
        let mut a = Assembler::new(&mut code_bytes);
        assert_eq!(a.patch(p1, LABEL), None);
        assert_eq!(a.patch(p2, LABEL), None);
        assert_eq!(a.patch(p3, LABEL), None);
        disassemble(&code_bytes[..len], vec![
            "je near 0000000002461357h",
            "jmp 0000000002461357h",
            "call 0000000002461357h",
        ]).unwrap();
        let mut a = Assembler::new(&mut code_bytes);
        assert_eq!(a.patch(p1, LABEL), Some(LABEL));
        assert_eq!(a.patch(p2, LABEL), Some(LABEL));
        assert_eq!(a.patch(p3, LABEL), Some(LABEL));
        disassemble(&code_bytes[..len], vec![
            "je near 0000000002461357h",
            "jmp 0000000002461357h",
            "call 0000000002461357h",
        ]).unwrap();
    }
}
