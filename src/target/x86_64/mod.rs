use super::super::buffer::{Buffer};

mod assembler;
pub use assembler::{Assembler, Label, Precision, Register, BinaryOp, ShiftOp, Condition, Width};
use Register::*;

mod lowerer;
pub use lowerer::{Lowerer, ALLOCATABLE_REGISTERS};

/**
 * In the System V amd64 calling convention, these registers must be preserved
 * by subroutines, as must `RSP`.
 */
pub const CALLEE_SAVES: [Register; 6] = [RB, RBP, R12, R13, R14, R15];

/**
 * In the System V amd64 calling convention, these registers may be
 * corrupted by subroutines.
 */
pub const CALLER_SAVES: [Register; 9] = [RDI, RSI, RD, RC, R8, R9, R10, R11, RA];
