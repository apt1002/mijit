use super::control_flow::{Register};

/// Beetle's address space.
/// V is the type of a non-compile-time-known variable.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum BeetleRegister {
    Ep,
    A,
    Sp,
    Rp,
    S0,
    R0,
    Throw,
    Bad,
    NotAddress,
}

impl Register for BeetleRegister {}

