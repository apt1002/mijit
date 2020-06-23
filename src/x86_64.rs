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

    /** Writes a single byte at the assembly pointer, incrementing it. */
    pub fn write_byte(&mut self, byte: u8) {
        self.buffer[self.pos] = byte;
        self.pos += 1;
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

    /** Writes a 32-bit signed immediate constant. */
    pub fn write_imm32(&mut self, immediate: i32) {
        self.write((immediate as u32) as u64, 4);
    }

    /** Writes a 32-bit displacement from `pos+4` to `target`. */
    pub fn write_rel32(&mut self, target: usize) {
        let disp = disp32(self.pos + 4, target);
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

    /** Conditional branch. */
    pub fn jump_if(&mut self, cc: Condition, is_true: bool, target: usize) {
        self.write_oo_0(cc.jump_if(is_true));
        self.write_rel32(target);
    }

    /** Unconditional jump to a register. */
    pub fn jump(&mut self, target: Register) {
        self.write_rom_1(0xE0FF40, target);
    }

    /** Unconditional jump to a constant. */
    pub fn const_jump(&mut self, target: usize) {
        self.write_ro_0(0xE940);
        self.write_rel32(target);
    }

    /** Unconditional call to a register. */
    pub fn call(&mut self, target: Register) {
        self.write_rom_1(0xD0FF40, target);
    }

    /** Unconditional call to a constant. */
    pub fn const_call(&mut self, target: usize) {
        self.write_ro_0(0xE840);
        self.write_rel32(target);
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
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use iced_x86::{Decoder, Formatter, NasmFormatter};

    /**
     * Disassemble the given x64_64 `code_bytes` as if they were at `code_ip`.
     */
    pub fn disassemble(code_bytes: &[u8], code_ip: u64) -> Vec<String> {
        let mut decoder = Decoder::new(64, code_bytes, 0);
        decoder.set_ip(code_ip);
        let mut formatter = NasmFormatter::new();
        decoder.iter().map(|instruction| {
            let ip = instruction.ip();
            let start = (ip - code_ip) as usize;
            let len = instruction.len() as usize;
            let bytes = code_bytes[start..][..len].iter().rev().map(
                |b| format!("{:02X}", b)
            ).collect::<Vec<String>>().join(" ");
            let mut assembly = String::with_capacity(80);
            formatter.format(&instruction, &mut assembly);
            format!("{:016X}   {:>32}   {:}", ip, bytes, assembly)
        }).collect()
    }

    #[test]
    fn test_disassemble() {
        let example_code = &[0x48, 0x89, 0x5C, 0x24, 0x10, 0x55];
        assert_eq!(disassemble(example_code, 0x10000000), [
            "0000000010000000                     10 24 5C 89 48   mov [rsp+10h],rbx",
            "0000000010000005                                 55   push rbp"
        ]);
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
        assert_eq!(disassemble(&code_bytes[..len], 0x10000000), [
            "0000000010000000                           C0 8B 40   mov eax,eax",
            "0000000010000003                           C9 8B 40   mov ecx,ecx",
            "0000000010000006                           D2 8B 40   mov edx,edx",
            "0000000010000009                           DB 8B 40   mov ebx,ebx",
            "000000001000000C                           ED 8B 40   mov ebp,ebp",
            "000000001000000F                           F6 8B 40   mov esi,esi",
            "0000000010000012                           FF 8B 40   mov edi,edi",
            "0000000010000015                           C0 8B 45   mov r8d,r8d",
            "0000000010000018                           C9 8B 45   mov r9d,r9d",
            "000000001000001B                           D2 8B 45   mov r10d,r10d",
            "000000001000001E                           DB 8B 45   mov r11d,r11d",
            "0000000010000021                           ED 8B 45   mov r13d,r13d",
            "0000000010000024                           F6 8B 45   mov r14d,r14d",
            "0000000010000027                           FF 8B 45   mov r15d,r15d",
        ]);
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
        assert_eq!(disassemble(&code_bytes[..len], 0x10000000), [
            "0000000010000000                  76 54 32 10 B9 41   mov r9d,76543210h",
            "0000000010000006                           D1 8B 45   mov r10d,r9d",
            "0000000010000009               12 34 56 78 90 89 45   mov [r8+12345678h],r10d",
            "0000000010000010               12 34 56 78 98 8B 45   mov r11d,[r8+12345678h]",
        ]);
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
        assert_eq!(disassemble(&code_bytes[..len], 0x10000000), [
            "0000000010000000                           CA 01 45   add r10d,r9d",
            "0000000010000003                           CA 09 45   or r10d,r9d",
            "0000000010000006                           CA 11 45   adc r10d,r9d",
            "0000000010000009                           CA 19 45   sbb r10d,r9d",
            "000000001000000C                           CA 21 45   and r10d,r9d",
            "000000001000000F                           CA 29 45   sub r10d,r9d",
            "0000000010000012                           CA 31 45   xor r10d,r9d",
            "0000000010000015                           CA 39 45   cmp r10d,r9d",
        ]);
    }

    /** Test that we can assemble all the different kinds of operation. */
    #[test]
    fn mode() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        a.op(Add, R10, R9);
        a.const_op(Add, R10, IMM);
        a.load_op(Add, R9, (R8, DISP));
        let len = a.label();
        assert_eq!(disassemble(&code_bytes[..len], 0x10000000), [
            "0000000010000000                           CA 01 45   add r10d,r9d",
            "0000000010000003               76 54 32 10 C2 81 41   add r10d,76543210h",
            "000000001000000A               12 34 56 78 88 03 45   add r9d,[r8+12345678h]",
        ]);
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
            a.jump_if(cc, true, target);
            a.jump_if(cc, false, target);
        }
        let len = a.label();
        assert_eq!(disassemble(&code_bytes[..len], 0x10000000), [
            "0000000010000000                  00 00 00 22 80 0F   jo near 0000000010000028h",
            "0000000010000006                  00 00 00 1C 81 0F   jno near 0000000010000028h",
            "000000001000000C                  00 00 00 16 81 0F   jno near 0000000010000028h",
            "0000000010000012                  00 00 00 10 80 0F   jo near 0000000010000028h",
            "0000000010000018                  00 00 00 0A 82 0F   jb near 0000000010000028h",
            "000000001000001E                  00 00 00 04 83 0F   jae near 0000000010000028h",
            "0000000010000024                  FF FF FF FE 83 0F   jae near 0000000010000028h",
            "000000001000002A                  FF FF FF F8 82 0F   jb near 0000000010000028h",
            "0000000010000030                  FF FF FF F2 84 0F   je near 0000000010000028h",
            "0000000010000036                  FF FF FF EC 85 0F   jne near 0000000010000028h",
            "000000001000003C                  FF FF FF E6 85 0F   jne near 0000000010000028h",
            "0000000010000042                  FF FF FF E0 84 0F   je near 0000000010000028h",
            "0000000010000048                  FF FF FF DA 86 0F   jbe near 0000000010000028h",
            "000000001000004E                  FF FF FF D4 87 0F   ja near 0000000010000028h",
            "0000000010000054                  FF FF FF CE 87 0F   ja near 0000000010000028h",
            "000000001000005A                  FF FF FF C8 86 0F   jbe near 0000000010000028h",
            "0000000010000060                  FF FF FF C2 88 0F   js near 0000000010000028h",
            "0000000010000066                  FF FF FF BC 89 0F   jns near 0000000010000028h",
            "000000001000006C                  FF FF FF B6 89 0F   jns near 0000000010000028h",
            "0000000010000072                  FF FF FF B0 88 0F   js near 0000000010000028h",
            "0000000010000078                  FF FF FF AA 8A 0F   jp near 0000000010000028h",
            "000000001000007E                  FF FF FF A4 8B 0F   jnp near 0000000010000028h",
            "0000000010000084                  FF FF FF 9E 8B 0F   jnp near 0000000010000028h",
            "000000001000008A                  FF FF FF 98 8A 0F   jp near 0000000010000028h",
            "0000000010000090                  FF FF FF 92 8C 0F   jl near 0000000010000028h",
            "0000000010000096                  FF FF FF 8C 8D 0F   jge near 0000000010000028h",
            "000000001000009C                  FF FF FF 86 8D 0F   jge near 0000000010000028h",
            "00000000100000A2                  FF FF FF 80 8C 0F   jl near 0000000010000028h",
            "00000000100000A8                  FF FF FF 7A 8E 0F   jle near 0000000010000028h",
            "00000000100000AE                  FF FF FF 74 8F 0F   jg near 0000000010000028h",
            "00000000100000B4                  FF FF FF 6E 8F 0F   jg near 0000000010000028h",
            "00000000100000BA                  FF FF FF 68 8E 0F   jle near 0000000010000028h",
        ]);
    }

    /** Test that we can assemble the different kinds of unconditional jump. */
    #[test]
    fn jump() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        a.jump(R8);
        a.const_jump(LABEL);
        let len = a.label();
        assert_eq!(disassemble(&code_bytes[..len], 0x10000000), [
            "0000000010000000                           E0 FF 41   jmp r8",
            "0000000010000003                  02 46 13 4E E9 40   jmp 0000000012461357h"
        ]);
    }

    /** Test that we can assemble the different kinds of call and return. */
    #[test]
    fn call_ret() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        a.call(R8);
        a.const_call(LABEL);
        a.ret();
        let len = a.label();
        assert_eq!(disassemble(&code_bytes[..len], 0x10000000), [
            "0000000010000000                           D0 FF 41   call r8",
            "0000000010000003                  02 46 13 4E E8 40   call 0000000012461357h",
            "0000000010000009                              C3 40   ret"
        ]);
    }

    /** Test that we can assemble "PUSH" and "POP". */
    #[test]
    fn push_pop() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        a.push(R8);
        a.pop(R9);
        let len = a.label();
        assert_eq!(disassemble(&code_bytes[..len], 0x10000000), [
            "0000000010000000                              50 41   push r8",
            "0000000010000002                              59 41   pop r9"
        ]);
    }
}
