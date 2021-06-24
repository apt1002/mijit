use crate::util::{AsUsize};
use super::{
    buffer, code,
    Patch, Label, Counter, Word, Pool, STATE_INDEX,
    Assembler, Precision, Register, BinaryOp, ShiftOp, Condition, Width,
    CALLEE_SAVES, ARGUMENTS, RESULTS,
};
use buffer::{Buffer, Mmap};
use code::{Action, TestOp, Global, Slot};
use Register::*;
use Precision::*;
use BinaryOp::*;
use ShiftOp::*;

//-----------------------------------------------------------------------------

/** The constants that [`Lowerer`] requires to be in the [`Pool`]. */
pub const CONSTANTS: [Word; 8] = [
    Word {u: 0},
    Word {u: 0}, // unused
    Word {u: 0}, // unused
    Word {u: 0}, // unused
    Word {u: 0}, // unused
    Word {u: 0}, // unused
    Word {u: 0}, // unused
    Word {u: 0}, // unused
];

/** The address of zero. */
const ZERO_ADDRESS: usize = 0;

/** The [`Register`] used for the pool pointer. */
const POOL: Register = R8;

/** The [`Register`] used as a temporary variable. */
const TEMP: Register = R12;

/**
 * The registers available for allocation. This omits:
 *  - `POOL`, which holds the pool base address.
 *  - `TEMP`, which is used as temporary workspace.
 */
// TODO: Write a test that compares this to `ALL_REGISTERS`.
pub const ALLOCATABLE_REGISTERS: [Register; 13] =
    [RA, RD, RC, RB, RBP, RSI, RDI, R9, R10, R11, R13, R14, R15];

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
    Global(Global),
    Slot(Slot),
}

impl From<Register> for Value {
    fn from(r: Register) -> Self {
        Value::Register(r)
    }
}

impl From<Global> for Value {
    fn from(g: Global) -> Self {
        Value::Global(g)
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
            code::Value::Global(global) => global.into(),
            code::Value::Slot(slot) => slot.into(),
        }
    }
}

//-----------------------------------------------------------------------------

pub struct Lowerer<B: Buffer> {
    /** The underlying [`Assembler`]. */
    a: Assembler<B>,
    /** The [`Pool`]. */
    pool: Pool,
    /** The number of stack-allocated spill [`Slot`]s. */
    slots_used: usize,
}

impl<B: Buffer> Lowerer<B> {
    pub fn new(pool: Pool) -> Self {
        let mut a = Assembler::new();
        // Fill the first cache line with useful constants.
        for &word in &CONSTANTS {
            a.write_imm64(unsafe {word.s});
        }
        Self {a, pool, slots_used: 0}
    }

    /** Apply `callback` to the contained [`Assembler`]. */
    pub fn use_assembler<T>(
        mut self,
        callback: impl FnOnce(Assembler<B>) -> std::io::Result<(Assembler<B>, T)>,
    ) -> std::io::Result<(Self, T)> {
        let (a, ret) = callback(self.a)?;
        self.a = a;
        Ok((self, ret))
    }

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

    /** Conditional branch. */
    fn jump_if(&mut self, cc: Condition, is_true: bool, target: &mut Label) {
        let patch = self.a.jump_if(cc, is_true, target.target());
        target.push(patch);
    }

    /** Unconditional jump to a constant. */
    fn const_jump(&mut self, target: &mut Label) {
        let patch = self.a.const_jump(target.target());
        target.push(patch);
    }

    /** Unconditional call to a constant. */
    #[allow(dead_code)]
    fn const_call(&mut self, target: &mut Label) {
        let patch = self.a.const_call(target.target());
        target.push(patch);
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

    /** Returns the base and offset of `global`. */
    fn global_address(&self, global: Global) -> (Register, i32) {
        (POOL, (self.pool.index_of_global(global) * 8) as i32)
    }

    /** Returns the base and offset of `counter`. */
    fn counter_address(&self, counter: Counter) -> (Register, i32) {
        (POOL, (self.pool.index_of_counter(counter) * 8) as i32)
    }

    /** Returns the base and offset of `slot` in the stack-allocated data. */
    fn slot_address(&self, slot: Slot) -> (Register, i32) {
        assert!(slot.0 < self.slots_used);
        (RSP, (((self.slots_used - 1) - slot.0) * 8) as i32)
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
            Value::Global(global) => {
                self.a.load(P64, reg, self.global_address(global));
                reg
            },
            Value::Slot(slot) => {
                self.a.load(P64, reg, self.slot_address(slot));
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
            Value::Global(global) => {
                self.a.load_op(op, prec, dest, self.global_address(global));
            },
            Value::Slot(slot) => {
                self.a.load_op(op, prec, dest, self.slot_address(slot));
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
            Value::Global(global) => {
                self.a.load_if(cc, is_true, prec, dest, self.global_address(global));
            },
            Value::Slot(slot) => {
                self.a.load_if(cc, is_true, prec, dest, self.slot_address(slot));
            },
        }
    }

    /** Select how to assemble an asymmetric `BinaryOp` such as `Sub`. */
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

    /** Select how to assemble a symmetric `BinaryOp` such as `Add`. */
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
        #[allow(clippy::if_same_then_else)]
        if !matches!(src1, Value::Register(_)) {
            // We get better code if `src1` is a Register, so swap with `src2`.
            self.asymmetric_binary(dest, src2, src1, callback);
        } else if src2 == Value::Register(dest) {
            // We get better code if `src1` is `dest`, so swap with `src2`.
            self.asymmetric_binary(dest, src2, src1, callback);
        } else {
            self.asymmetric_binary(dest, src1, src2, callback);
        }
    }

    /** Select how to assemble a shift `BinaryOp` such as `Shl`. */
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

    /** Select how to assemble a conditional `BinaryOp` such as `Lt` or `Max`. */
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
}

//-----------------------------------------------------------------------------

impl<B: Buffer> super::Lower for Lowerer<B> {
    fn pool(&self) -> &Pool { &self.pool }

    fn pool_mut(&mut self) -> &mut Pool { &mut self.pool }

    fn slots_used(&mut self) -> &mut usize { &mut self.slots_used }

    fn here(&self) -> Label { Label::new(Some(self.a.get_pos())) }

    fn patch(&mut self, patch: Patch, old_target: Option<usize>, new_target: Option<usize>) {
        self.a.patch(patch, old_target, new_target);
    }

    fn jump(&mut self, label: &mut Label) {
        self.const_jump(label);
    }

    fn lower_prologue(&mut self) {
        if CALLEE_SAVES.len() & 1 != 1 {
            // Adjust alignment of RSP to be 16-byte aligned.
            self.a.push(CALLEE_SAVES[0]);
        }
        for &r in &CALLEE_SAVES {
            self.a.push(r);
        }
        self.move_(POOL, ARGUMENTS[0]);
        self.move_(STATE_INDEX, ARGUMENTS[1]);
    }

    fn lower_epilogue(&mut self) {
        self.move_(RESULTS[0], STATE_INDEX);
        for &r in CALLEE_SAVES.iter().rev() {
            self.a.pop(r);
        }
        if CALLEE_SAVES.len() & 1 != 1 {
            // Adjust alignment of RSP to be 16-byte aligned.
            self.a.pop(CALLEE_SAVES[0]);
        }
        self.a.ret();
    }

    fn lower_test_op(
        &mut self,
        guard: (code::TestOp, Precision),
        false_label: &mut Label,
    ) {
        let (test_op, prec) = guard;
        match test_op {
            TestOp::Bits(discriminant, mask, value) => {
                self.const_(prec, TEMP, i64::from(mask));
                self.value_op(And, prec, TEMP, discriminant);
                self.const_op(Cmp, prec, TEMP, value);
                self.jump_if(Condition::Z, false, false_label);
            },
            TestOp::Lt(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.const_op(Cmp, prec, discriminant, value);
                self.jump_if(Condition::L, false, false_label);
            },
            TestOp::Ge(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.const_op(Cmp, prec, discriminant, value);
                self.jump_if(Condition::GE, false, false_label);
            },
            TestOp::Ult(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.const_op(Cmp, prec, discriminant, value);
                self.jump_if(Condition::B, false, false_label);
            },
            TestOp::Uge(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.const_op(Cmp, prec, discriminant, value);
                self.jump_if(Condition::AE, false, false_label);
            },
            TestOp::Eq(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.const_op(Cmp, prec, discriminant, value);
                self.jump_if(Condition::Z, false, false_label);
            },
            TestOp::Ne(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP);
                self.const_op(Cmp, prec, discriminant, value);
                self.jump_if(Condition::NZ, false, false_label);
            },
            TestOp::Always => {},
        };
    }

    fn lower_unary_op(
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

    fn lower_binary_op(
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
                        Value::Global(global) => {
                            l.a.load_mul(prec, dest, l.global_address(global));
                        },
                        Value::Slot(slot) => {
                            l.a.load_mul(prec, dest, l.slot_address(slot));
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
                    l.a.load_pc_relative_if(Condition::L, false, prec, dest, ZERO_ADDRESS);
                });
            },
            code::BinaryOp::Ult => {
                self.compare_binary(prec, dest, src1, src2, |l, dest, _| {
                    l.a.const_preserving_flags(prec, dest, -1);
                    l.a.load_pc_relative_if(Condition::B, false, prec, dest, ZERO_ADDRESS);
                });
            },
            code::BinaryOp::Eq => {
                self.compare_binary(prec, dest, src1, src2, |l, dest, _| {
                    l.a.const_preserving_flags(prec, dest, -1);
                    l.a.load_pc_relative_if(Condition::Z, false, prec, dest, ZERO_ADDRESS);
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

    fn lower_action(
        &mut self,
        action: Action,
    ) {
        match action {
            Action::Move(dest, src) => {
                // `dest_to_register()` would generate less efficient code.
                match dest {
                    code::Value::Register(dest) => {
                        let src = self.src_to_register(src, dest);
                        self.move_(dest, src);
                    },
                    code::Value::Global(global) => {
                        let src = self.src_to_register(src, TEMP);
                        self.a.store(P64, self.global_address(global), src);
                    },
                    code::Value::Slot(slot) => {
                        let src = self.src_to_register(src, TEMP);
                        self.a.store(P64, self.slot_address(slot), src);
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
                *self.slots_used() += 1;
                self.a.push(src);
            },
            Action::Pop(dest) => {
                let dest = dest.into();
                assert!(*self.slots_used() >= 1);
                self.a.pop(dest);
                *self.slots_used() -= 1;
            },
            Action::DropMany(n) => {
                assert!(*self.slots_used() >= n);
                self.a.const_op(BinaryOp::Add, P64, RSP, (n as i32) * 8);
                *self.slots_used() -= n;
            },
            Action::Debug(x) => {
                let x = self.src_to_register(x, TEMP);
                self.a.debug(x);
            },
        };
    }

    fn lower_count(&mut self, counter: Counter) {
        // This could be a single instruction.
        self.a.load(P64, TEMP, self.counter_address(counter));
        self.a.const_op(BinaryOp::Add, P64, TEMP, 1);
        self.a.store(P64, self.counter_address(counter), TEMP);
    }
}

//-----------------------------------------------------------------------------

impl super::Execute for Lowerer<Mmap> {
    fn execute<T>(
        mut self,
        label: &Label,
        callback: impl FnOnce(super::ExecuteFn, &mut Pool) -> T,
    ) -> std::io::Result<(Self, T)> {
        let target = label.target().expect("Label is not defined");
        let pool = &mut self.pool;
        let (a, ret) = self.a.use_buffer(|b| {
            b.execute(|bytes| {
                let f = unsafe { std::mem::transmute(&bytes[target]) };
                callback(f, pool)
            })
        })?;
        self.a = a;
        Ok((self, ret))
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use std::mem::{size_of};

    use super::*;
    use super::super::assembler::tests::{disassemble};
    use super::super::Condition::Z;
    use super::super::super::{Lower as _};

    const LABEL: usize = 0x02461357;

    #[test]
    fn allocatable_regs() {
        for &r in &ALLOCATABLE_REGISTERS {
            assert_ne!(r, POOL);
            assert_ne!(r, TEMP);
        }
    }

    /** Test that we can patch jumps and calls. */
    #[test]
    fn steal() {
        let pool = Pool::new(0);
        let mut lo = Lowerer::<buffer::VecU8>::new(pool);
        let start = lo.here().target().unwrap();
        let mut label = Label::new(None);
        lo.jump_if(Z, true, &mut label);
        lo.const_jump(&mut label);
        lo.const_call(&mut label);
        disassemble(&lo.a, start, vec![
            "je near 0FFFFFFFF80000046h",
            "jmp 0FFFFFFFF8000004Ch",
            "call 0FFFFFFFF80000052h",
        ]).unwrap();
        let mut new_label = Label::new(Some(LABEL));
        lo.steal(&mut new_label, &mut label);
        label = new_label;
        disassemble(&lo.a, start, vec![
            "je near 0000000002461357h",
            "jmp 0000000002461357h",
            "call 0000000002461357h",
        ]).unwrap();
        let mut new_label = Label::new(Some(LABEL));
        lo.steal(&mut new_label, &mut label);
        disassemble(&lo.a, start, vec![
            "je near 0000000002461357h",
            "jmp 0000000002461357h",
            "call 0000000002461357h",
        ]).unwrap();
    }

    #[test]
    fn constants() {
        assert_eq!(CONSTANTS[ZERO_ADDRESS / size_of::<Word>()], Word {u: 0});
    }
}
