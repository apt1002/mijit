use super::{Register, Variable, Precision, UnaryOp, BinaryOp, Width, AliasMask};

/// Called by [`Action::Debug`].
#[no_mangle]
pub extern fn debug_word(x: u64) {
    println!("Debug: {:#018x}", x);
}

/// An imperative instruction.
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
    Load(Register, (Variable, Width), AliasMask),
    /// dest <- addr; \[addr] <- \[src]
    /// `dest` exists to make the optimizer allocate a temporary register.
    Store(Register, Variable, (Variable, Width), AliasMask),
    /// sp <- sp - 16; \[sp] <- src1; \[sp + 8] <- src2
    /// If either `src` is `None`, push a dead value.
    Push(Option<Variable>, Option<Variable>),
    /// dest1 <- \[sp]; dest2 <- \[sp + 8]; sp <- sp + 16
    /// If either `dest` is `None`, pop a dead value.
    Pop(Option<Register>, Option<Register>),
    /// sp <- sp + 16*n
    DropMany(usize),
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
            Action::Load(dest, (addr, width), _) =>
                write!(f, "Load_{:?} {:?}, [{:?}]", width, dest, addr),
            Action::Store(dest, src, (addr, width), _) =>
                write!(f, "Store_{:?} {:?}, {:?}, [{:?}]", width, dest, src, addr),
            Action::Push(src1, src2) =>
                write!(f, "Push ({:?}, {:?})", src1, src2),
            Action::Pop(dest1, dest2) =>
                write!(f, "Pop ({:?}, {:?})", dest1, dest2),
            Action::DropMany(n) =>
                write!(f, "DropMany 2*{:?}", n),
            Action::Debug(src) =>
                write!(f, "Debug {:?}", src),
        }
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::collections::{HashMap};

    /// An emulator for a subset of Mijit code, useful for testing
    /// automatically-generated code.
    pub struct Emulator {
        variables: Vec<Variable>,
    }

    impl Emulator {
        pub fn new(variables: Vec<Variable>) -> Self {
            Emulator {variables}
        }

        pub fn execute(&self, actions: &[Action]) -> HashMap<Variable, i64> {
            let mut state: HashMap<Variable, i64> = self.variables.iter().enumerate().map(|(i, v)| {
                (*v, 1000 + i as i64)
            }).collect();
            for action in actions {
                match action {
                    &Action::Move(dest, src) => {
                        let x = *state.get(&src).expect("Missing from state");
                        state.insert(dest, x);
                    },
                    &Action::Constant(Precision::P64, dest, imm) => {
                        state.insert(dest.into(), imm);
                    },
                    &Action::Unary(UnaryOp::Not, Precision::P64, dest, src) => {
                        let x = *state.get(&src).expect("Missing from state");
                        state.insert(dest.into(), !x);
                    },
                    &Action::Binary(BinaryOp::Add, Precision::P64, dest, src1, src2) => {
                        let x = *state.get(&src1).expect("Missing from state");
                        let y = *state.get(&src2).expect("Missing from state");
                        state.insert(dest.into(), x + y);
                    },
                    _ => panic!("Don't know how to execute {:#?}", action),
                }
            }
            state
        }
    }

    /// Ensure the linker symbol `debug_word` is included in the binary.
    #[test]
    fn not_really_a_test() {
        debug_word(0);
    }
}
