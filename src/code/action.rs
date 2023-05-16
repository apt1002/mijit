use super::{Register, Variable, Precision, UnaryOp, BinaryOp, Width};

/// Called by [`Action::Debug`].
#[no_mangle]
pub extern fn debug_word(x: u64) {
    println!("Debug: {:#018x}", x);
}

/// An imperative instruction.
///
/// The destination register (where applicable) is on the left.
#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub enum Action {
    /// dest <- src
    Move(Variable, Variable),

    /// dest <- constant
    Constant(Precision, Register, i64),

    /// dest <- op(src)
    Unary(UnaryOp, Precision, Register, Variable),

    /// dest <- op(src1, src2)
    Binary(BinaryOp, Precision, Register, Variable, Variable),

    /// dest <- \[addr]
    Load(Register, (Variable, Width)),

    /// dest <- addr; \[addr] <- \[src]
    ///
    /// If you later `Load` or `Store` via `addr`, the behaviour is undefined.
    Store(Register, Variable, (Variable, Width)),

    /// dest <- src1
    /// Memory accesses via `dest` will happen later than memory accesses via
    /// `src2`, if they might be to the same location.
    ///
    /// If you later `Load` or `Store` via `src2`, the behaviour is undefined.
    /// Note that `Send` says nothing about accesses via `src1`.
    Send(Register, Variable, Variable),

    /// sp <- sp - 16; \[sp] <- src1; \[sp + 8] <- src2
    ///
    /// If either `src` is `None`, push a dead value.
    /// Note that this creates two [`Slot`]s.
    ///
    /// [`Slot`]: super::Slot
    Push(Option<Variable>, Option<Variable>),

    /// sp <- sp + 16*n
    ///
    /// Note that this drops `2*n` [`Slot`]s.
    ///
    /// [`Slot`]: super::Slot
    Drop(usize),

    /// Pass `src` to [`debug_word()`].
    Debug(Variable),
}

impl std::fmt::Debug for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Action::Move(dest, src) =>
                write!(f, "Move {:?}, {:?}", dest, src),
            Action::Constant(prec, dest, c) =>
                write!(f, "Constant_{:?} {:?}, {:x?}", prec, dest, c),
            Action::Unary(op, prec, dest, src) =>
                write!(f, "{:?}_{:?} {:?}, {:?}", op, prec, dest, src),
            Action::Binary(op, prec, dest, src1, src2) =>
                write!(f, "{:?}_{:?} {:?}, {:?}, {:?}", op, prec, dest, src1, src2),
            Action::Load(dest, (addr, width)) =>
                write!(f, "Load_{:?} {:?}, [{:?}]", width, dest, addr),
            Action::Store(dest, src, (addr, width)) =>
                write!(f, "Store_{:?} {:?}, {:?}, [{:?}]", width, dest, src, addr),
            Action::Send(dest, src1, src2) =>
                write!(f, "Send {:?}, {:?}, {:?}", dest, src1, src2),
            Action::Push(src1, src2) =>
                write!(f, "Push ({:?}, {:?})", src1, src2),
            Action::Drop(n) =>
                write!(f, "Drop 2*{:?}", n),
            Action::Debug(src) =>
                write!(f, "Debug {:?}", src),
        }
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    /// Ensure the linker symbol `debug_word` is included in the binary.
    #[test]
    fn not_really_a_test() {
        debug_word(0);
    }
}
