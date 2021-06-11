/**
 * All AArch64 registers, except R18, which we avoid on [ARM's advice]. For our
 * purposes, `IP0` (=`R16`) and `IP1` (=`R17`) are ordinary registers.
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
    R0 = 0,
    R1 = 1,
    R2 = 2,
    R3 = 3,
    R4 = 4,
    R5 = 5,
    R6 = 6,
    R7 = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
    R16 = 16,
    R17 = 17,
    R19 = 19,
    R20 = 20,
    R21 = 21,
    R22 = 22,
    R23 = 23,
    R24 = 24,
    R25 = 25,
    R26 = 26,
    R27 = 27,
    R28 = 28,
    RFP = 29,
    RLR = 30,
    RZR = 31,
}

use Register::*;

/**
 * The stack pointer register `RSP` shares an encoding with the zero register
 * `RZR`.
 */
pub const RSP: Register = RZR;

//-----------------------------------------------------------------------------

/**
 * Represents the precision of an arithmetic operation.
 * With P32, the arithmetic is performed with 32-bit precision, and written
 * into the bottom 32 bits of the destination. The top 32 bits are 0.
 */
// TODO: Make portable and move to `mod target`.
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
}

//-----------------------------------------------------------------------------

