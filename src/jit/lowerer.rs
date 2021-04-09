use super::{code, x86_64};

use crate::util::{AsUsize};
use x86_64::{Register, Precision, BinaryOp, ShiftOp, Condition, Width, Assembler, Label};
use code::{Action, TestOp, Slot};
use Register::*;
use Precision::*;
use BinaryOp::*;
use ShiftOp::*;

//-----------------------------------------------------------------------------

/**
 * The registers available for allocation. This differs from
 * [`x86_64::ALL_REGISTERS`] because:
 *  - `RC` is used as temporary workspace.
 *  - `R8` holds the pool base address.
 */
// TODO: Write a test that compares this to `ALL_REGISTERS`.
pub const ALLOCATABLE_REGISTERS: [Register; 13] =
    [RA, RD, RC, RB, RBP, RSI, RDI, R9, R10, R11, R13, R14, R15];

const TEMP: Register = R12;

impl From<code::Register> for Register {
    fn from(r: code::Register) -> Self {
        ALLOCATABLE_REGISTERS[r.as_usize()]
    }
}

impl From<code::Width> for Width {
    fn from(w: code::Width) -> Self {
        use code::Width::*;
        match w {
            One => Width::U8,
            Two => Width::U16,
            Four => Width::U32,
            Eight => Width::U64,
        }
    }
}

//-----------------------------------------------------------------------------

/**
 * A low-level analogue of `code::Value`, which can hold unallocatable
 * [`Register`]s.
 */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
enum Value {
    Register(Register),
    Slot(Slot),
}

impl From<Register> for Value {
    fn from(r: Register) -> Self {
        Value::Register(r)
    }
}

impl From<Slot> for Value {
    fn from(s: Slot) -> Self {
        Value::Slot(s)
    }
}

impl From<code::Register> for Value {
    fn from(r: code::Register) -> Self {
        Value::Register(r.into())
    }
}

impl From<code::Value> for Value {
    fn from(v: code::Value) -> Self {
        match v {
            code::Value::Register(reg) => reg.into(),
            code::Value::Slot(slot) => slot.into(),
        }
    }
}

//-----------------------------------------------------------------------------

pub struct Lowerer<'a> {
    // TODO: Remove "pub".
    pub a: Assembler<'a>,
}

impl <'a> Lowerer<'a> {
    /** Put `value` in `dest`. */
    fn const_(&mut self, prec: Precision, dest: impl Into<Register>, value: i64) {
        let dest = dest.into();
        self.a.const_(prec, dest, value);
    }

    /** Apply `op` to `dest` and `value`. */
    fn const_op(&mut self, op: BinaryOp, prec: Precision, dest: impl Into<Register>, value: i32) {
        let dest = dest.into();
        self.a.const_op(op, prec, dest, value);
    }

    /** Move `src` to `dest` if they are different. */
    fn move_(&mut self, dest: impl Into<Register>, src: impl Into<Register>) {
        let dest = dest.into();
        let src = src.into();
        if dest != src {
            self.a.move_(P64, dest, src);
        }
    }

    /** Move `src` to `TEMP` if `src` is `dest`. */
    fn move_away_from(&mut self, src: impl Into<Value>, dest: impl Into<Register>) -> Value {
        let src = src.into();
        let dest = dest.into();
        if src == dest.into() {
            self.move_(TEMP, dest);
            TEMP.into()
        } else {
            src
        }
    }

    /** Returns the offset of `slot` in the persistent data. */
    fn slot_offset(&self, slot: Slot) -> i32 {
        // TODO: Factor out pool index calculation.
        ((slot.0 + 1) * 8) as i32
    }

    /** Load `slot` into `dest`. */
    fn load_slot(&mut self, dest: impl Into<Register>, slot: Slot) {
        let dest = dest.into();
        self.a.load(P64, dest, (R8, self.slot_offset(slot)));
    }

    /** Store `src` into `slot`. */
    fn store_slot(&mut self, slot: Slot, src: impl Into<Register>) {
        let src = src.into();
        self.a.store(P64, (R8, self.slot_offset(slot)), src);
    }

    /**
     * If `src` is a Register, returns it, otherwise loads it into `reg` and
     * returns `reg`.
     */
    fn src_to_register(&mut self, src: impl Into<Value>, reg: impl Into<Register>) -> Register {
        let src = src.into();
        let reg = reg.into();
        match src {
            Value::Register(src) => src,
            Value::Slot(slot) => {
                self.load_slot(reg, slot);
                reg
            },
        }
    }

    /**
     * Calls `a.op()` or `a.load_op()` depending on whether `src` is a Register
     * or a Slot.
     */
    fn value_op(&mut self, op: BinaryOp, prec: Precision, dest: impl Into<Register>, src: impl Into<Value>) {
        let dest = dest.into();
        let src = src.into();
        match src {
            Value::Register(src) => {
                self.a.op(op, prec, dest, src);
            },
            Value::Slot(index) => {
                self.a.load_op(op, prec, dest, (R8, self.slot_offset(index)));
            },
        }
    }

    fn value_move_if(&mut self, cc: Condition, is_true: bool, prec: Precision, dest: impl Into<Register>, src: impl Into<Value>) {
        let dest = dest.into();
        let src = src.into();
        match src {
            Value::Register(src) => {
                self.a.move_if(cc, is_true, prec, dest, src);
            },
            Value::Slot(index) => {
                self.a.load_if(cc, is_true, prec, dest, (R8, self.slot_offset(index)));
            },
        }
    }


    /**
     * Assemble code that branches to `false_label` if `test_op` is false.
     */
    pub fn lower_test_op(
        &mut self,
        test_op: code::TestOp,
        prec: Precision,
        false_label: &mut Label,
    ) {
        match test_op {
            TestOp::Bits(discriminant, mask, value) => {
                self.const_(prec, TEMP, mask as i64);
                self.value_op(And, prec, TEMP, discriminant);
                self.const_op(Cmp, prec, TEMP, value);
                self.a.jump_if(Condition::Z, false, false_label);
            },
            TestOp::Lt(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.const_op(Cmp, prec, discriminant, value);
                self.a.jump_if(Condition::L, false, false_label);
            },
            TestOp::Ge(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.const_op(Cmp, prec, discriminant, value);
                self.a.jump_if(Condition::GE, false, false_label);
            },
            TestOp::Ult(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.const_op(Cmp, prec, discriminant, value);
                self.a.jump_if(Condition::B, false, false_label);
            },
            TestOp::Uge(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.const_op(Cmp, prec, discriminant, value);
                self.a.jump_if(Condition::AE, false, false_label);
            },
            TestOp::Eq(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.const_op(Cmp, prec, discriminant, value);
                self.a.jump_if(Condition::Z, false, false_label);
            },
            TestOp::Ne(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.const_op(Cmp, prec, discriminant, value);
                self.a.jump_if(Condition::NZ, false, false_label);
            },
            TestOp::Always => {},
        };
    }
    
    /**
     * Assemble code to perform the given `unary_op`.
     */
    pub fn lower_unary_op(
        &mut self,
        unary_op: code::UnaryOp,
        prec: Precision,
        dest: code::Register,
        src: code::Value,
    ) {
        match unary_op {
            code::UnaryOp::Abs => {
                let src = self.move_away_from(src, dest);
                self.const_(prec, dest, 0);
                self.value_op(Sub, prec, dest, src);
                self.value_move_if(Condition::L, true, prec, dest, src);
            },
            code::UnaryOp::Negate => {
                let src = self.move_away_from(src, dest);
                self.const_(prec, dest, 0);
                self.value_op(Sub, prec, dest, src);
            },
            code::UnaryOp::Not => {
                let src = self.src_to_register(src, dest);
                self.move_(dest, src);
                self.const_op(Xor, prec, dest, -1);
            },
        };
    }

    /** Select how to assemble an asymmetric BinaryOp such as `Sub`. */
    fn asymmetric_binary(
        &mut self,
        dest: impl Into<Register>,
        src1: impl Into<Value>,
        src2: impl Into<Value>,
        callback: impl FnOnce(&mut Self, Register, Value),
    ) {
        let dest = dest.into();
        let src2 = self.move_away_from(src2, dest);
        let src1 = self.src_to_register(src1, dest);
        self.move_(dest, src1);
        callback(self, dest, src2);
    }

    /** Select how to assemble a symmetric BinaryOp such as `Add`. */
    fn symmetric_binary(
        &mut self,
        dest: impl Into<Register>,
        src1: impl Into<Value>,
        src2: impl Into<Value>,
        callback: impl FnOnce(&mut Self, Register, Value),
    ) {
        let dest = dest.into();
        let src1 = src1.into();
        let src2 = src2.into();
        if let Value::Slot(_) = src1 {
            // We get better code if `src1` is not a Slot, so swap with `src2`.
            self.asymmetric_binary(dest, src2, src1, callback);
        } else if src2 == Value::Register(dest) {
            // We get better code if `src1` is `dest`, so swap with `src2`.
            self.asymmetric_binary(dest, src2, src1, callback);
        } else {
            self.asymmetric_binary(dest, src1, src2, callback);
        }
    }

    /** Select how to assemble a shift BinaryOp such as `Shl`. */
    fn shift_binary(&mut self, op: ShiftOp, prec: Precision, dest: impl Into<Register>, src1: impl Into<Value>, src2: impl Into<Value>) {
        let dest = dest.into();
        let src1 = src1.into();
        let src2 = src2.into();
        let save_rc = src2 != Value::Register(RC);
        if save_rc {
            self.move_(TEMP, RC);
        }
        let src2 = self.src_to_register(src2, RC);
        self.move_(RC, src2);
        let src1 = self.src_to_register(src1, dest);
        self.move_(dest, src1);
        self.a.shift(op, prec, dest);
        if save_rc {
            self.move_(RC, TEMP);
        }
    }

    /** Select how to assemble a conditional BinaryOp such as `Lt` or `Max`. */
    fn compare_binary(
        &mut self,
        prec: Precision,
        dest: impl Into<Register>,
        src1: impl Into<Value>,
        src2: impl Into<Value>,
        callback: impl FnOnce(&mut Self, Register, Register),
    ) {
        let dest = dest.into();
        let src1 = self.src_to_register(src1, TEMP);
        let src2 = src2.into();
        self.value_op(Cmp, prec, src1, src2);
        callback(self, dest, src1);
    }

    /**
     * Assemble code to perform the given `binary_op`.
     */
    pub fn lower_binary_op(
        &mut self,
        binary_op: code::BinaryOp,
        prec: Precision,
        dest: code::Register,
        src1: code::Value,
        src2: code::Value,
    ) {
        match binary_op {
            code::BinaryOp::Add => {
                self.symmetric_binary(dest, src1, src2, |l, dest, src| {
                    l.value_op(Add, prec, dest, src);
                });
            },
            code::BinaryOp::Sub => {
                self.asymmetric_binary(dest, src1, src2, |l, dest, src| {
                    l.value_op(Sub, prec, dest, src);
                });
            },
            code::BinaryOp::Mul => {
                self.symmetric_binary(dest, src1, src2, |l, dest, src| {
                    match src {
                        Value::Register(src) => {
                            l.a.mul(prec, dest, src);
                        },
                        Value::Slot(index) => {
                            l.a.load_mul(prec, dest, (R8, l.slot_offset(index)));
                        },
                    }
                });
            },
            // TODO: Define what happens when you shift too far.
            code::BinaryOp::Lsl => {
                self.shift_binary(Shl, prec, dest, src1, src2);
            },
            code::BinaryOp::Lsr => {
                self.shift_binary(Shr, prec, dest, src1, src2);
            },
            code::BinaryOp::Asr => {
                self.shift_binary(Sar, prec, dest, src1, src2);
            },
            code::BinaryOp::And => {
                self.symmetric_binary(dest, src1, src2, |l, dest, src| {
                    l.value_op(And, prec, dest, src);
                });
            },
            code::BinaryOp::Or => {
                self.symmetric_binary(dest, src1, src2, |l, dest, src| {
                    l.value_op(Or, prec, dest, src);
                });
            },
            code::BinaryOp::Xor => {
                self.symmetric_binary(dest, src1, src2, |l, dest, src| {
                    l.value_op(Xor, prec, dest, src);
                });
            },
            code::BinaryOp::Lt => {
                self.compare_binary(prec, dest, src1, src2, |l, dest, _| {
                    l.a.const_preserving_flags(prec, dest, -1);
                    l.a.load_if(Condition::L, false, prec, dest, (R8, 0));
                });
            },
            code::BinaryOp::Ult => {
                self.compare_binary(prec, dest, src1, src2, |l, dest, _| {
                    l.a.const_preserving_flags(prec, dest, -1);
                    l.a.load_if(Condition::B, false, prec, dest, (R8, 0));
                });
            },
            code::BinaryOp::Eq => {
                self.compare_binary(prec, dest, src1, src2, |l, dest, _| {
                    l.a.const_preserving_flags(prec, dest, -1);
                    l.a.load_if(Condition::Z, false, prec, dest, (R8, 0));
                });
            },
            code::BinaryOp::Max => {
                self.compare_binary(prec, dest, src1, src2, |l, dest, src1| {
                    l.move_(dest, src1);
                    l.value_move_if(Condition::L, true, prec, dest, src2);
                });
            },
            code::BinaryOp::Min => {
                self.compare_binary(prec, dest, src1, src2, |l, dest, src1| {
                    l.move_(dest, src1);
                    l.value_move_if(Condition::G, true, prec, dest, src2);
                });
            },
        };
    }

    /**
     * Assemble code to perform the given `action`.
     */
    pub fn lower_action(
        &mut self,
        action: Action,
    ) {
        match action {
            Action::Move(dest, src) => {
                // `dest_to_register()` would generate less efficient code.
                match dest {
                    code::Value::Register(dest) => {
                        match src {
                            code::Value::Register(src) => {
                                self.move_(dest, src);
                            },
                            code::Value::Slot(index) => {
                                self.load_slot(dest, index);
                            },
                        }
                    },
                    code::Value::Slot(index) => {
                        let src = self.src_to_register(src, TEMP);
                        self.store_slot(index, src);
                    },
                }
            },
            Action::Constant(prec, dest, value) => {
                self.const_(prec, dest, value);
            },
            Action::Unary(op, prec, dest, src) => {
                self.lower_unary_op(op, prec, dest, src);
            },
            Action::Binary(op, prec, dest, src1, src2) => {
                self.lower_binary_op(op, prec, dest, src1, src2);
            },
            Action::Load(dest, (addr, width), _) => {
                let dest = dest.into();
                let addr = self.src_to_register(addr, dest);
                let width = width.into();
                self.a.load_narrow(P64, width, dest, (addr, 0));
            },
            Action::Store(dest, src, (addr, width), _) => {
                let dest = Register::from(dest);
                let src = self.src_to_register(src, TEMP);
                let addr = self.src_to_register(addr, dest);
                self.move_(dest, addr);
                let width = width.into();
                self.a.store_narrow(width, (addr, 0), src);
            },
            Action::Push(src) => {
                let src = self.src_to_register(src, TEMP);
                self.a.push(src);
            },
            Action::Pop(dest) => {
                let dest = dest.into();
                self.a.pop(dest);
            },
            Action::Debug(x) => {
                let x = self.src_to_register(x, TEMP);
                self.a.debug(x);
            },
        };
    }
}
