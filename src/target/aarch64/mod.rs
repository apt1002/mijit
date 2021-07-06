use super::{buffer, code, Patch, Label, Counter, Pool, STATE_INDEX, Lower, ExecuteFn, Execute};
use buffer::{Mmap};

mod enums;
pub use enums::{Register, RSP, Condition, ALL_CONDITIONS, MemOp, ShiftOp, LogicOp};

mod assembler;
pub use assembler::{Assembler, logic_immediate};
use Register::*;

mod lowerer;
pub use lowerer::{Lowerer, ALLOCATABLE_REGISTERS};

/**
 * In the AArch64 calling convention, these registers must be preserved by
 * subroutines, as must `RFP` and `RSP`.
 */
pub const CALLEE_SAVES: [Register; 10] = [R19, R20, R21, R22, R23, R24, R25, R26, R27, R28];

/**
 * In the AArch64  calling convention, these registers may be corrupted by
 * subroutines, as may `RLR`. We include `RIP0` and `RIP1`.
 */
pub const CALLER_SAVES: [Register; 18] = [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14, R15, R16, R17];

/**
 * In the AArch64 calling convention, these registers hold the integer-
 * or pointer-type function arguments.
 */
pub const ARGUMENTS: [Register; 8] = [R0, R1, R2, R3, R4, R5, R6, R7];

/**
 * In the AArch64 calling convention, these registers hold the integer-
 * or pointer-type function results.
 */
pub const RESULTS: [Register; 8] = [R0, R1, R2, R3, R4, R5, R6, R7];

/** The aarch64/libc compilation target. */
pub struct Target;

impl super::Target for Target {
    type Lowerer = Lowerer<Mmap>;

    const NUM_REGISTERS: usize = ALLOCATABLE_REGISTERS.len();

    fn lowerer(&self, pool: super::Pool) -> Self::Lowerer {
        Lowerer::new(pool)
    }
}
