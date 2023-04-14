use super::code::{Register, Variable, Precision, UnaryOp, BinaryOp, Width, Action};

/// Annotates a [`Node`] of a [`Dataflow`] graph.
///
/// `Node`: super::Node
/// `Dataflow`: super::Dataflow
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(u8)]
pub enum Op {
    /// Represents a control-flow decision.
    Guard,
    /// A no-op used on entry to a Dataflow graph.
    Input,
    Constant(i64),
    Unary(Precision, UnaryOp),
    Binary(Precision, BinaryOp),
    Load(Width),
    Store(Width),
    Debug,
}

impl Op {
    /// Aggregates this [`Op`] with the specified outputs and inputs to make an
    /// [`Action`].
    /// Panics if the `Op` is a `Guard`.
    pub fn to_action(self, out: Option<Register>, ins: &[Variable]) -> Action {
        match self {
            Op::Guard => panic!("Cannot convert a guard to an action"),
            Op::Input => panic!("Cannot convert an input to an action"),
            Op::Constant(c) => {
                assert_eq!(ins.len(), 0);
                Action::Constant(Precision::P64, out.unwrap(), c)
            },
            Op::Unary(prec, op) => {
                assert_eq!(ins.len(), 1);
                Action::Unary(op, prec, out.unwrap(), ins[0])
            },
            Op::Binary(prec, op) => {
                assert_eq!(ins.len(), 2);
                Action::Binary(op, prec, out.unwrap(), ins[0], ins[1])
            },
            Op::Load(width) => {
                assert_eq!(ins.len(), 1);
                Action::Load(out.unwrap(), (ins[0], width))
            },
            Op::Store(width) => {
                assert_eq!(ins.len(), 2);
                Action::Store(out.unwrap(), ins[0], (ins[1], width))
            },
            Op::Debug => {
                assert!(out.is_none());
                assert_eq!(ins.len(), 1);
                Action::Debug(ins[0])
            },
        }
    }
}
