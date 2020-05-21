use super::control_flow::{Address};

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Variable;

/// Beetle's address space.
/// V is the type of a non-compile-time-known variable.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum BeetleAddress {
    Ep,
    A,
    Sp,
    Rp,
    S0,
    R0,
    Throw,
    Bad,
    NotAddress,
    Memory(Variable), // TODO: work out what "Variable" really is.
}

impl Address for BeetleAddress {
    fn can_alias(&self, other: &Self) -> bool {
        match self {
            &BeetleAddress::Memory(_) => match other {
                &BeetleAddress::Memory(_) => true,
                _ => false,
            },
            _ => false,
        }
    }
}
