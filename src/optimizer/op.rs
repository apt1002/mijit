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
     * Aggregates this Op with the specified output and input [`Value`]s to
     * make an [`Action`].
     * Returns `None` if `self` is [`Op::Convention`].
     * Panics if the address of an [`Op::Store`] is not a [`Register`].
     */
    pub fn to_action(self, outs: &[Register], ins: &[Value]) -> Option<Action> {
        match self {
            Op::Convention => None,
            Op::Constant(c) => {
                assert_eq!(outs.len(), 1);
                assert_eq!(ins.len(), 0);
                Some(Action::Constant(Precision::P64, outs[0], c))
            },
            Op::Unary(prec, op) => {
                assert_eq!(outs.len(), 1);
                assert_eq!(ins.len(), 1);
                Some(Action::Unary(op, prec, outs[0], ins[0]))
            },
            Op::Binary(prec, op) => {
                assert_eq!(outs.len(), 1);
                assert_eq!(ins.len(), 2);
                Some(Action::Binary(op, prec, outs[0], ins[0], ins[1]))
            },
            Op::Load(width, alias) => {
                assert_eq!(outs.len(), 1);
                assert_eq!(ins.len(), 1);
                Some(Action::Load(outs[0], (ins[0], width), alias))
            },
            Op::Store(width, alias) => {
                assert_eq!(outs.len(), 0);
                assert_eq!(ins.len(), 2);
                // FIXME: Add a destination [`Register`] to [`Action::Store`],
                // and allow the address operand to be a general [`Value`].
                // The address gets copied into the destination `Register`.
                match ins[1] {
                    Value::Register(addr) => {
                        Some(Action::Store(ins[0], (addr, width), alias))
                    },
                    Value::Slot(_) => panic!("Address must be a Register"),
                }
            },
            Op::Push => {
                assert_eq!(outs.len(), 0);
                assert_eq!(ins.len(), 1);
                Some(Action::Push(ins[0]))
            },
            Op::Pop => {
                assert_eq!(outs.len(), 1);
                assert_eq!(ins.len(), 0);
                Some(Action::Pop(outs[0]))
            },
            Op::Debug => {
                assert_eq!(outs.len(), 0);
                assert_eq!(ins.len(), 1);
                Some(Action::Debug(ins[0]))
            },
        }
    }
}
