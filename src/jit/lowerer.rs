use super::{code, x86_64};
use x86_64::*;
use code::{Action, TestOp, Precision, Value};
use Register::*;
use Precision::*;
use BinaryOp::*;
use ShiftOp::*;


/**
 * The registers available for allocation. This differs from
 * `x86_64::ALL_REGISTERS` because:
 *  - `RC` is used as temporary workspace.
 *  - `R8` holds the pool base address.
 */
// TODO: Write a test that compares this to `ALL_REGISTERS`.
pub const ALLOCATABLE_REGISTERS: [Register; 13] =
    [RA, RD, RC, RB, RBP, RSI, RDI, R9, R10, R11, R13, R14, R15];

const TEMP: Register = R12;

pub struct Lowerer<'a> {
    pub a: Assembler<'a>,
}

impl <'a> Lowerer<'a> {
    /** Move `src` to `dest` if they are different. */
    fn move_(&mut self, dest: Register, src: Register) {
        if dest != src {
            self.a.move_(P64, dest, src);
        }
    }

    /** Move `src` to `TEMP` if `src` is `dest`. */
    fn move_away_from(&mut self, src: Value, dest: Register) -> Value {
        if src == Value::Register(dest) {
            self.move_(TEMP, dest);
            TEMP.into()
        } else {
            src
        }
    }

    /** Returns the offset of slot `index` in the persistent data. */
    fn slot_offset(&self, index: usize) -> i32 {
        // TODO: Factor out pool index calculation.
        ((index + 1) * 8) as i32
    }

    /** Load slot `index` into `dest`. */
    fn load_slot(&mut self, dest: Register, index: usize) {
        self.a.load(P64, dest, (R8, self.slot_offset(index)));
    }

    /** Store `src` into slot `index`. */
    fn store_slot(&mut self, index: usize, src: Register) {
        self.a.store(P64, (R8, self.slot_offset(index)), src);
    }

    /**
     * If `src` is a Register, returns it, otherwise loads it into `reg` and
     * returns `reg`.
     */
    fn src_to_register(&mut self, src: Value, reg: Register) -> Register {
        match src {
            Value::Register(src) => src,
            Value::Slot(index) => {
                self.load_slot(reg, index);
                reg
            },
        }
    }

    /**
     * If `dest` is a Register, passes it to `callback`, otherwise passes `TEMP`
     * to `callback` then stores it.
     */
    fn dest_to_register(&mut self, dest: Value, callback: impl FnOnce(&mut Lowerer<'a>, Register)) {
        match dest {
            Value::Register(dest) => {
                callback(self, dest);
            },
            Value::Slot(index) => {
                callback(self, TEMP);
                self.store_slot(index, TEMP);
            },
        }
    }

    /**
     * Calls `a.op()` or `a.load_op()` depending on whether `src` is a Register
     * or a Slot.
     */
    fn value_op(&mut self, op: BinaryOp, prec: Precision, dest: Register, src: Value) {
        match src {
            Value::Register(src) => {
                self.a.op(op, prec, dest, src);
            },
            Value::Slot(index) => {
                self.a.load_op(op, prec, dest, (R8, self.slot_offset(index)));
            },
        }
    }

    fn value_move_if(&mut self, cc: Condition, is_true: bool, prec: Precision, dest: Register, src: Value) {
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
                self.a.const_(prec, TEMP, mask as i64);
                self.value_op(And, prec, TEMP, discriminant);
                self.a.const_op(Cmp, prec, TEMP, value);
                self.a.jump_if(Condition::Z, false, false_label);
            },
            TestOp::Lt(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.a.const_op(Cmp, prec, discriminant, value);
                self.a.jump_if(Condition::L, false, false_label);
            },
            TestOp::Ge(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.a.const_op(Cmp, prec, discriminant, value);
                self.a.jump_if(Condition::GE, false, false_label);
            },
            TestOp::Ult(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.a.const_op(Cmp, prec, discriminant, value);
                self.a.jump_if(Condition::B, false, false_label);
            },
            TestOp::Uge(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.a.const_op(Cmp, prec, discriminant, value);
                self.a.jump_if(Condition::AE, false, false_label);
            },
            TestOp::Eq(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.a.const_op(Cmp, prec, discriminant, value);
                self.a.jump_if(Condition::Z, false, false_label);
            },
            TestOp::Ne(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.a.const_op(Cmp, prec, discriminant, value);
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
        dest: Register,
        src: Value,
    ) {
        match unary_op {
            code::UnaryOp::Abs => {
                let src = self.move_away_from(src, dest);
                self.a.const_(prec, dest, 0);
                self.value_op(Sub, prec, dest, src);
                self.value_move_if(Condition::L, true, prec, dest, src);
            },
            code::UnaryOp::Negate => {
                let src = self.move_away_from(src, dest);
                self.a.const_(prec, dest, 0);
                self.value_op(Sub, prec, dest, src);
            },
            code::UnaryOp::Not => {
                let src = self.src_to_register(src, dest);
                self.move_(dest, src);
                self.a.const_op(Xor, prec, dest, -1);
            },
        };
    }

    /** Select how to assemble an asymmetric BinaryOp such as `Sub`. */
    fn asymmetric_binary(
        &mut self,
        dest: Register,
        src1: Value,
        src2: Value,
        callback: impl FnOnce(&mut Self, Register, Value),
    ) {
        let src2 = self.move_away_from(src2, dest);
        let src1 = self.src_to_register(src1, dest);
        self.move_(dest, src1);
        callback(self, dest, src2);
    }

    /** Select how to assemble a symmetric BinaryOp such as `Add`. */
    fn symmetric_binary(
        &mut self,
        dest: Register,
        src1: Value,
        src2: Value,
        callback: impl FnOnce(&mut Self, Register, Value),
    ) {
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
    fn shift_binary(&mut self, op: ShiftOp, prec: Precision, dest: Register, src1: Value, src2: Value) {
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
        dest: Register,
        src1: Value,
        src2: Value,
        callback: impl FnOnce(&mut Self, Register, Register),
    ) {
        let src1 = self.src_to_register(src1, TEMP);
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
        dest: Register,
        src1: Value,
        src2: Value,
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

    fn lower_width(width: code::Width) -> x86_64::Width {
        use code::Width::*;
        match width {
            One => x86_64::Width::U8,
            Two => x86_64::Width::U16,
            Four => x86_64::Width::U32,
            Eight => x86_64::Width::U64,
        }
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
                    Value::Register(dest) => {
                        match src {
                            Value::Register(src) => {
                                if dest != src {
                                    self.a.move_(P64, dest, src);
                                }
                            },
                            Value::Slot(index) => {
                                self.load_slot(dest, index);
                            },
                        }
                    },
                    Value::Slot(index) => {
                        let src = self.src_to_register(src, TEMP);
                        self.store_slot(index, src);
                    },
                }
            },
            Action::Constant(prec, dest, value) => {
                self.a.const_(prec, dest, value);
            },
            Action::Unary(op, prec, dest, src) => {
                self.lower_unary_op(op, prec, dest, src);
            },
            Action::Binary(op, prec, dest, src1, src2) => {
                self.lower_binary_op(op, prec, dest, src1, src2);
            },
            Action::Load(dest, (addr, width), _) => {
                let width = Self::lower_width(width);
                let addr = self.src_to_register(addr, dest);
                self.a.load_narrow(P64, width, dest, (addr, 0));
            },
            Action::Store(src, (addr, width), _) => {
                let width = Self::lower_width(width);
                let src = self.src_to_register(src, TEMP);
                self.a.store_narrow(width, (addr, 0), src);
            },
            Action::Push(src) => {
                let src = self.src_to_register(src, TEMP);
                self.a.push(src);
            },
            Action::Pop(dest) => {
                self.dest_to_register(dest, |l, dest| {
                    l.a.pop(dest);
                });
            },
            Action::Debug(x) => {
                let x = self.src_to_register(x, TEMP);
                self.a.debug(x);
            },
        };
    }
}
