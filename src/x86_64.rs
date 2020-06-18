use std::ops::{DerefMut};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Register(u8);

pub const A: Register = Register(0);
pub const D: Register = Register(1);
pub const C: Register = Register(2);
pub const B: Register = Register(3);
// SP is not a general-purpose register.
pub const BP: Register = Register(5);
pub const SI: Register = Register(6);
pub const DI: Register = Register(7);
pub const R8: Register = Register(8);
pub const R9: Register = Register(9);
pub const R10: Register = Register(10);
pub const R11: Register = Register(11);
// R12 is not a general-purpose register.
pub const R13: Register = Register(13);
pub const R14: Register = Register(14);
pub const R15: Register = Register(15);

impl Register {
    pub fn mask(&self) -> u64 {
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
        ][self.0 as usize]
    }
}

pub const ALLOCATABLE_REGISTERS: [Register; 14] = [
    A, D, C, B, BP, SI, DI, R8, R9, R10, R11, R13, R14, R15
];

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
 * An assembler.
 *
 * The low-level memory address of `buffer` definitely won't change while the
 * Assembler exists, but it could change at other times, e.g. because the
 * containing Vec grows and gets reallocated. Therefore, be wary of absolute
 * memory addresses. Assembler itself never uses them, and instead represents
 * addresses as displacements from the beginning of `buffer`.
 *
 * Patterns are described [here](doc/x86.rs). A typical pattern is "ROOM"
 * meaning a REX byte, two opcode bytes, and a ModR/M byte.
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

    /** Writes an instruction with pattern "OO", i.e. two opcode bytes. */
    pub fn write_oo(&mut self, opcode: u64) {
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

    /** Move constant to memory. */
    pub fn const_store(&mut self, dest: (Register, i32), imm: i32) {
        self.write_rom_1(0x80C740, dest.0);
        self.write_imm32(dest.1);
        self.write_imm32(imm);
    }

    /** Move constant to register. */
    pub fn const_(&mut self, dest: Register, imm: i32) {
        self.write_ro_1(0xB840, dest);
        self.write_imm32(imm);
    }

    /** Add register to register. */
    pub fn add(&mut self, dest: Register, src: Register) {
        self.write_rom_2(0xC00140, dest, src);
    }

    /** Add constant to register. */
    pub fn const_add(&mut self, dest: Register, imm: i32) {
        self.write_rom_1(0xC08140, dest);
        self.write_imm32(imm);
    }

    /** Add a memory location to a register. */
    pub fn load_add(&mut self, dest: Register, src: (Register, i32)) {
        self.write_rom_2(0x800340, src.0, dest);
        self.write_imm32(src.1);
    }

    /** Add a register to a memory location. */
    pub fn load_add_store(&mut self, dest: (Register, i32), src: Register) {
        self.write_rom_2(0x800140, dest.0, src);
        self.write_imm32(dest.1);
    }

    /** Add a constant to a memory location. */
    pub fn load_const_add_store(&mut self, dest: (Register, i32), imm: i32) {
        self.write_rom_1(0x808140, dest.0);
        self.write_imm32(dest.1);
        self.write_imm32(imm);
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

    #[test]
    fn regs() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        for &r in &ALLOCATABLE_REGISTERS {
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

    #[test]
    fn mov() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        a.const_(R9, IMM);
        a.mov(R10, R9);
        a.store((R8, DISP), R10);
        a.load(R11, (R8, DISP));
        a.const_store((R8, DISP), IMM);
        let len = a.label();
        assert_eq!(disassemble(&code_bytes[..len], 0x10000000), [
            "0000000010000000                  76 54 32 10 B9 41   mov r9d,76543210h",
            "0000000010000006                           D1 8B 45   mov r10d,r9d",
            "0000000010000009               12 34 56 78 90 89 45   mov [r8+12345678h],r10d",
            "0000000010000010               12 34 56 78 98 8B 45   mov r11d,[r8+12345678h]",
            "0000000010000017   76 54 32 10 12 34 56 78 80 C7 41   mov dword [r8+12345678h],76543210h",
        ]);
    }

    #[test]
    fn add() {
        let mut code_bytes = vec![0u8; 0x1000];
        let mut a = Assembler::new(&mut code_bytes);
        a.add(R10, R9);
        a.const_add(R10, IMM);
        a.load_add(R9, (R8, DISP));
        a.load_add_store((R8, DISP), R10);
        a.load_const_add_store((R8, DISP), IMM);
        let len = a.label();
        assert_eq!(disassemble(&code_bytes[..len], 0x10000000), [
            "0000000010000000                           CA 01 45   add r10d,r9d",
            "0000000010000003               76 54 32 10 C2 81 41   add r10d,76543210h",
            "000000001000000A               12 34 56 78 88 03 45   add r9d,[r8+12345678h]",
            "0000000010000011               12 34 56 78 90 01 45   add [r8+12345678h],r10d",
            "0000000010000018   76 54 32 10 12 34 56 78 80 81 41   add dword [r8+12345678h],76543210h",
        ]);
    }
}
