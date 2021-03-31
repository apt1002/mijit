use super::code::{Register, Value, Precision, UnaryOp, BinaryOp, Width, AliasMask, Action};

/** Compactly represents a kind of [`Action`]. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(u8)]
pub enum Op {
    /** A no-op used at the external boundaries of a Dataflow graph. */
    Convention,
    Constant(i64),
    Unary(Precision, UnaryOp),
    Binary(Precision, BinaryOp),
    Load(Width, AliasMask),
    Store(Width, AliasMask),
    Push,
    Pop,
    Debug,
}

impl Op {
    /**
     * Aggregates this [`Op`] with the specified output and input [`Value`]s to
     * make an [`Action`].
     * Returns `None` if `self` is [`Op::Convention`].
     * Panics if the `Op` is a `Convention`.
     */
    pub fn to_action(self, outs: &[Register], ins: &[Value]) -> Action {
        match self {
            Op::Convention => panic!("Cannot execute a Convention"),
            Op::Constant(c) => {
                assert_eq!(outs.len(), 1);
                assert_eq!(ins.len(), 0);
                Action::Constant(Precision::P64, outs[0], c)
            },
            Op::Unary(prec, op) => {
                assert_eq!(outs.len(), 1);
                assert_eq!(ins.len(), 1);
                Action::Unary(op, prec, outs[0], ins[0])
            },
            Op::Binary(prec, op) => {
                assert_eq!(outs.len(), 1);
                assert_eq!(ins.len(), 2);
                Action::Binary(op, prec, outs[0], ins[0], ins[1])
            },
            Op::Load(width, alias) => {
                assert_eq!(outs.len(), 1);
                assert_eq!(ins.len(), 1);
                Action::Load(outs[0], (ins[0], width), alias)
            },
            Op::Store(width, alias) => {
                assert_eq!(outs.len(), 1);
                assert_eq!(ins.len(), 2);
                Action::Store(outs[0], ins[0], (ins[1], width), alias)
            },
            Op::Push => {
                assert_eq!(outs.len(), 0);
                assert_eq!(ins.len(), 1);
                Action::Push(ins[0])
            },
            Op::Pop => {
                assert_eq!(outs.len(), 1);
                assert_eq!(ins.len(), 0);
                Action::Pop(outs[0])
            },
            Op::Debug => {
                assert_eq!(outs.len(), 0);
                assert_eq!(ins.len(), 1);
                Action::Debug(ins[0])
            },
        }
    }
}
