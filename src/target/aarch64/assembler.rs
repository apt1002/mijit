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
