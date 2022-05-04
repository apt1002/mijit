/// Represents the precision of an arithmetic operation.
/// With `P32`, the arithmetic is performed with 32-bit precision, and written
/// into the bottom 32 bits of the destination. The top 32 bits are 0.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Precision {
    P32 = 0,
    P64 = 1,
}

impl Precision {
    pub fn bits(self) -> usize { 32 << (self as usize) }
}

//-----------------------------------------------------------------------------

/// Unary arithmetic operations.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum UnaryOp {
    Abs,
    Negate,
    Not,
    // TODO: Uxt, Sxt (#12).
}

/// Binary arithmetic operations.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    Lsl,
    Lsr,
    Asr,
    And,
    Or,
    Xor,
    Lt,
    Ult,
    Eq,
    Max, // TODO: Unsigned too?
    Min, // TODO: Unsigned too?
}

/// The number of bytes transferred by a memory access.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(u8)]
pub enum Width {
    One = 0,
    Two = 1,
    Four = 2,
    Eight = 3,
}

//-----------------------------------------------------------------------------

/// Indicates which parts of memory overlap with each other. More precisely,
/// indicates whether the value loaded from one address can be affected by a
/// store to another address.
///
/// Every [`Action::Load`] and [`Action::Store`] instruction is annotated with
/// an `AliasMask`, which is internally a bitmask. If the `AliasMask`s of two
/// memory accesses have any set bits in common, and one of them is a `Store`,
/// and if the optmizer cannot prove that they access different addresses, then
/// the optimizer will not reorder the two instructions.
///
/// It is allowed, but unhelpful, for every `AliasMask` to have all bits set.
/// This will force all memory accesses to occur in the order they are written.
///
/// If all stores to some address precede all loads from it, then it is
/// encouraged to give all those memory accesses an `AliasMask` of zero.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct AliasMask(pub u32);

impl AliasMask {
    /// Tests whether `self` and `other` have any bits in common.
    pub fn can_alias(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

impl std::ops::BitAnd for AliasMask {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        AliasMask(self.0 & rhs.0)
    }
}

impl std::ops::BitOr for AliasMask {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        AliasMask(self.0 | rhs.0)
    }
}

impl std::ops::BitXor for AliasMask {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        AliasMask(self.0 ^ rhs.0)
    }
}
