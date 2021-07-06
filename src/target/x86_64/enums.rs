/**
 * All x86_64 registers that can be used interchangeably in our chosen subset
 * of x86_64.
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

pub const ALL_REGISTERS: [Register; 16] = [RA, RC, RD, RB, RSP, RBP, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15];

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

pub const ALL_BINARY_OPS: [BinaryOp; 8] = [Add, Or, Adc, Sbb, And, Sub, Xor, Cmp];

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

use ShiftOp::*;

pub const ALL_SHIFT_OPS: [ShiftOp; 7] = [Rol, Ror, Rcl, Rcr, Shl, Shr, Sar];

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

use Condition::*;

pub const ALL_CONDITIONS: [Condition; 16] = [O, NO, B, AE, Z, NZ, BE, A, S, NS, P, NP, L, GE, LE, G];

impl Condition {
    pub fn invert(self) -> Self {
        ALL_CONDITIONS[(self as usize) ^ 1]
    }

    pub fn move_if(self) -> u64 {
        0xC0400F40 | ((self as u64) << 16)
    }

    pub fn load_if(self) -> u64 {
        0x80400F40 | ((self as u64) << 16)
    }

    pub fn load_pc_relative_if(self) -> u64 {
        0x00400F40 | ((self as u64) << 16)
    }

    pub fn jump_if(self) -> u64 {
        0x800F | ((self as u64) << 8)
    }
}

//-----------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Width {U8, S8, U16, S16, U32, S32, U64, S64}

use Width::*;

pub const ALL_WIDTHS: [Width; 8] = [U8, S8, U16, S16, U32, S32, U64, S64];
