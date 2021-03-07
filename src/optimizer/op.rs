/** Compactly represents a kind of [`Action`]. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(u8)]
pub enum Op {
    Convention,
    Constant,
    Abs,
    Negate,
    Not,
    Add,
    Sub,
    Mul,
    Lsl,
    Lsr,
    Asr,
    And,
    Or,
    Xor,
    Lt,
    Ult,
    Eq,
    Max,
    Min,
    Load,
    Store,
    Push,
    Pop,
    Debug,
}

impl crate::util::AsUsize for Op {
    fn as_usize(self) -> usize { self as usize }
}
