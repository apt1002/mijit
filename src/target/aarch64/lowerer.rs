use crate::util::{AsUsize};
use super::{
    buffer, code,
    Patch, Label, Counter, Pool, STATE_INDEX,
    Shift,
    Register, RSP, Condition, MemOp, ShiftOp, AddOp, LogicOp,
    Assembler, CALLEE_SAVES, CALLER_SAVES, ARGUMENTS, RESULTS,
};
use Register::*;
use MemOp::*;
use AddOp::*;
use LogicOp::*;
use ShiftOp::*;
use Width::*;
use buffer::{Buffer, Mmap};
use code::{Precision, Action, TestOp, UnaryOp, BinaryOp, Width, Global, Slot, debug_word};
use Precision::*;

/** The [`Register`] used for the pool pointer. */
const POOL: Register = RLR;

/** A [`Register`] used as a temporary variable. */
const TEMP0: Register = R16;

/** A [`Register`] used as a temporary variable. */
const TEMP1: Register = R17;

/**
 * The registers available for allocation. This omits:
 *  - `POOL`, which holds the pool base address.
 *  - `TEMP0`, which is used as temporary workspace.
 *  - `TEMP1`, which is used as temporary workspace.
 *  - `RFP`, which is used as a frame pointer.
 *  - `RZR`, obviously.
 */
// TODO: Write a test that compares this to `ALL_REGISTERS`.
pub const ALLOCATABLE_REGISTERS: [Register; 27] = [
    R0, R1, R2, R3, R4, R5, R6, R7,
    R8, R9, R10, R11, R12, R13, R14, R15,
    R18, R19, R20, R21, R22, R23,
    R24, R25, R26, R27, R28,
];

impl From<code::Register> for Register {
    fn from(r: code::Register) -> Self {
        ALLOCATABLE_REGISTERS[r.as_usize()]
    }
}

//-----------------------------------------------------------------------------

/**
 * A low-level analogue of `code::Variable`, which can hold unallocatable
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

impl From<code::Variable> for Value {
    fn from(v: code::Variable) -> Self {
        match v {
            code::Variable::Register(reg) => reg.into(),
            code::Variable::Global(global) => global.into(),
            code::Variable::Slot(slot) => slot.into(),
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
        Self {a: Assembler::new(), pool, slots_used: 0}
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
    fn const_(&mut self, dest: impl Into<Register>, value: u64) {
        let dest = dest.into();
        self.a.const_(dest, value);
    }

    /** Conditional branch. */
    fn jump_if(&mut self, cc: Condition, target: &mut Label) {
        let patch = self.a.jump_if(cc, target.target());
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

    /** Assemble `op` with no shift. */
    fn add(&mut self, op: AddOp, prec: Precision, dest: impl Into<Register>, src1: impl Into<Register>, src2: impl Into<Register>) {
        self.a.shift_add(op, dest.into(), src1.into(), src2.into(), Shift::new(prec, 0).unwrap());
    }

    /** Compare `src1` to `src2` and set condition flags. */
    fn cmp(&mut self, prec: Precision, src1: impl Into<Register>, src2: impl Into<Register>) {
        self.add(SUBS, prec, RZR, src1, src2);
    }

    /**
     * Compare `src` to `constant` and set condition flags.
     * `temp` is corrupted.
     */
    fn const_cmp(&mut self, prec: Precision, src: impl Into<Register>, constant: i64, temp: Register) {
        if constant.abs() < 0x1000 {
            if constant >= 0 {
                self.a.const_add(SUBS, prec, RZR, src.into(), constant as u64);
            } else {
                self.a.const_add(ADDS, prec, RZR, src.into(), -constant as u64);
            }
        } else {
            self.const_(temp, constant as u64);
            self.cmp(prec, src, temp);
        }
    }

    /** Assemble `op` with no shift. */
    fn logic(&mut self, op: LogicOp, prec: Precision, not: bool, dest: impl Into<Register>, src1: impl Into<Register>, src2: impl Into<Register>) {
        self.a.shift_logic(op, not, dest.into(), src1.into(), src2.into(), Shift::new(prec, 0).unwrap());
    }

    /** Move `src` to `dest` if they are different. */
    fn move_(&mut self, dest: impl Into<Register>, src: impl Into<Register>) {
        let dest = dest.into();
        let src = src.into();
        if dest != src {
            self.logic(ORR, P64, false, dest, RZR, src);
        }
    }

    /**
     * Access 8 bytes at `address`, which must be 8-byte aligned.
     * Corrupts `temp`. If `op` is `LDR` or `LDRS`, `temp` can be `dest`.
     */
    fn mem(&mut self, op: MemOp, data: Register, address: (Register, u64), temp: Register) {
        let (base, offset) = address;
        // The low bits of `offset` fit in an immediate constant.
        const IMM_BITS: u64 = 12 + 3;
        assert_eq!(offset & 7, 0);
        let offset_high = offset >> IMM_BITS;
        let offset_low = offset - (offset_high << IMM_BITS);
        let base = if offset_high == 0 {
            // Only the low bits are used.
            base
        } else {
            // Handle the high bits separately.
            // TODO: Use an `LDR` with a shifted register offset.
            self.const_(temp, offset_high);
            self.a.shift_add(ADD, temp, base, temp, Shift::new(P64, IMM_BITS).unwrap());
            temp
        };
        self.a.mem(op, Eight, data, (base, offset_low as i64));
    }

    /** Returns the base and offset of `global`. */
    fn global_address(&self, global: Global) -> (Register, u64) {
        (POOL, (self.pool.index_of_global(global) * 8) as u64)
    }

    /** Returns the base and offset of `counter`. */
    fn counter_address(&self, counter: Counter) -> (Register, u64) {
        (POOL, (self.pool.index_of_counter(counter) * 8) as u64)
    }

    /** Returns the base and offset of `slot` in the stack-allocated data. */
    fn slot_address(&self, slot: Slot) -> (Register, u64) {
        assert!(slot.0 < self.slots_used);
        (RSP, (((self.slots_used - 1) - slot.0) * 8) as u64)
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
                self.mem(LDR, reg, self.global_address(global), reg);
                reg
            },
            Value::Slot(slot) => {
                self.mem(LDR, reg, self.slot_address(slot), reg);
                reg
            },
        }
    }

    /** Assemble code to perform the given `unary_op`. */
    fn unary_op(
        &mut self,
        unary_op: UnaryOp,
        prec: Precision,
        dest: code::Register,
        src: code::Variable,
    ) {
        let dest = dest.into();
        let src = self.src_to_register(src, dest);
        match unary_op {
            code::UnaryOp::Abs => {
                self.add(SUBS, prec, TEMP0, RZR, src);
                self.a.csel(prec, Condition::LE, dest, src, TEMP0);
            },
            code::UnaryOp::Negate => {
                let src = self.src_to_register(src, dest);
                self.add(SUB, prec, dest, RZR, src);
            },
            code::UnaryOp::Not => {
                let src = self.src_to_register(src, dest);
                self.logic(EOR, prec, true, dest, RZR, src);
            },
        };
    }

    /** Assemble code to perform the given `binary_op`. */
    fn binary_op(
        &mut self,
        binary_op: BinaryOp,
        prec: Precision,
        dest: code::Register,
        src1: code::Variable,
        src2: code::Variable,
    ) {
        let dest = dest.into();
        let src1 = self.src_to_register(src1, TEMP0);
        let src2 = self.src_to_register(src2, TEMP1);
        match binary_op {
            code::BinaryOp::Add => {
                self.add(ADD, prec, dest, src1, src2);
            },
            code::BinaryOp::Sub => {
                self.add(SUB, prec, dest, src1, src2);
            },
            code::BinaryOp::Mul => {
                self.a.mul(prec, dest, src1, src2);
            },
            // TODO: Define what happens when you shift too far.
            code::BinaryOp::Lsl => {
                self.a.shift(LSL, prec, dest, src1, src2);
            },
            code::BinaryOp::Lsr => {
                self.a.shift(LSR, prec, dest, src1, src2);
            },
            code::BinaryOp::Asr => {
                self.a.shift(ASR, prec, dest, src1, src2);
            },
            code::BinaryOp::And => {
                self.logic(AND, prec, false, dest, src1, src2);
            },
            code::BinaryOp::Or => {
                self.logic(ORR, prec, false, dest, src1, src2);
            },
            code::BinaryOp::Xor => {
                self.logic(EOR, prec, false, dest, src1, src2);
            },
            code::BinaryOp::Lt => {
                self.cmp(prec, src1, src2);
                self.a.const_(dest, !0);
                self.a.csel(prec, Condition::LT, dest, dest, RZR);
            },
            code::BinaryOp::Ult => {
                self.cmp(prec, src1, src2);
                self.a.const_(dest, !0);
                self.a.csel(prec, Condition::CC, dest, dest, RZR);
            },
            code::BinaryOp::Eq => {
                self.cmp(prec, src1, src2);
                self.a.const_(dest, !0);
                self.a.csel(prec, Condition::EQ, dest, dest, RZR);
            },
            code::BinaryOp::Max => {
                self.cmp(prec, src1, src2);
                self.a.csel(prec, Condition::GT, dest, src1, src2);
            },
            code::BinaryOp::Min => {
                self.cmp(prec, src1, src2);
                self.a.csel(prec, Condition::LE, dest, src1, src2);
            },
        };
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

    fn prologue(&mut self) {
        self.a.push(RFP, RLR);
        self.a.const_add(ADD, P64, RFP, RSP, 0);
        for rs in CALLEE_SAVES.chunks(2).rev() {
            self.a.push(rs[0], rs[1]);
        }
        self.move_(POOL, ARGUMENTS[0]);
        self.move_(STATE_INDEX, ARGUMENTS[1]);
    }

    fn epilogue(&mut self) {
        self.move_(RESULTS[0], STATE_INDEX);
        for rs in CALLEE_SAVES.chunks(2) {
            self.a.pop(rs[0], rs[1]);
        }
        self.a.pop(RFP, RLR);
        self.a.ret(RLR);
    }

    fn test_op(
        &mut self,
        guard: (TestOp, Precision),
        false_label: &mut Label,
    ) {
        let (test_op, prec) = guard;
        // We can't assume a conditional branch can jump more than 1MB.
        // Therefore, conditionally branch past an unconditional branch.
        let skip = &mut Label::new(None);
        match test_op {
            TestOp::Bits(discriminant, mask, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP0);
                self.const_(TEMP1, i64::from(mask) as u64);
                self.logic(AND, prec, false, TEMP0, discriminant, TEMP1);
                self.const_cmp(prec, TEMP0, i64::from(value), TEMP1);
                self.jump_if(Condition::EQ, skip);
                self.const_jump(false_label);
            },
            TestOp::Lt(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP0);
                self.const_cmp(prec, discriminant, i64::from(value), TEMP1);
                self.jump_if(Condition::LT, skip);
                self.const_jump(false_label);
            },
            TestOp::Ge(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP0);
                self.const_cmp(prec, discriminant, i64::from(value), TEMP1);
                self.jump_if(Condition::GE, skip);
                self.const_jump(false_label);
            },
            TestOp::Ult(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP0);
                self.const_cmp(prec, discriminant, i64::from(value), TEMP1);
                self.jump_if(Condition::CC, skip);
                self.const_jump(false_label);
            },
            TestOp::Uge(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP0);
                self.const_cmp(prec, discriminant, i64::from(value), TEMP1);
                self.jump_if(Condition::CS, skip);
                self.const_jump(false_label);
            },
            TestOp::Eq(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP0);
                self.const_cmp(prec, discriminant, i64::from(value), TEMP1);
                self.jump_if(Condition::EQ, skip);
                self.const_jump(false_label);
            },
            TestOp::Ne(discriminant, value) => {
                let discriminant = self.src_to_register(discriminant, TEMP0);
                self.const_cmp(prec, discriminant, i64::from(value), TEMP1);
                self.jump_if(Condition::NE, skip);
                self.const_jump(false_label);
            },
            TestOp::Always => {},
        };
        self.define(skip);
    }

    fn action(
        &mut self,
        action: Action,
    ) {
        match action {
            Action::Move(dest, src) => {
                // `dest_to_register()` would generate less efficient code.
                match dest {
                    code::Variable::Register(dest) => {
                        let src = self.src_to_register(src, dest);
                        self.move_(dest, src);
                    },
                    code::Variable::Global(global) => {
                        let src = self.src_to_register(src, TEMP0);
                        self.mem(STR, src, self.global_address(global), TEMP1);
                    },
                    code::Variable::Slot(slot) => {
                        let src = self.src_to_register(src, TEMP0);
                        self.mem(STR, src, self.slot_address(slot), TEMP1);
                    },
                }
            },
            Action::Constant(prec, dest, value) => {
                let value = match prec {
                    P32 => u64::from(value as u32),
                    P64 => value as u64,
                };
                self.const_(dest, value as u64);
            },
            Action::Unary(op, prec, dest, src) => {
                self.unary_op(op, prec, dest, src);
            },
            Action::Binary(op, prec, dest, src1, src2) => {
                self.binary_op(op, prec, dest, src1, src2);
            },
            Action::Load(dest, (addr, width), _) => {
                let dest = dest.into();
                let addr = self.src_to_register(addr, dest);
                self.a.mem(LDR, width, dest, (addr, 0));
            },
            Action::Store(dest, src, (addr, width), _) => {
                let dest = Register::from(dest);
                let src = self.src_to_register(src, TEMP0);
                let addr = self.src_to_register(addr, dest);
                self.move_(dest, addr);
                self.a.mem(STR, width, src, (addr, 0));
            },
            Action::Push(src1, src2) => {
                let src1 = src1.map_or(RZR, |src1| self.src_to_register(src1, TEMP0));
                let src2 = src2.map_or(RZR, |src2| self.src_to_register(src2, TEMP1));
                *self.slots_used() += 2;
                self.a.push(src1, src2);
            },
            Action::Pop(dest1, dest2) => {
                assert!(*self.slots_used() >= 2);
                if dest1.is_none() && dest2.is_none() {
                    self.a.const_add(ADD, P64, RSP, RSP, 16);
                } else {
                    let dest1 = dest1.map_or(RZR, Register::from);
                    let dest2 = dest2.map_or(RZR, Register::from);
                    self.a.pop(dest1, dest2);
                }
                *self.slots_used() -= 2;
            },
            Action::DropMany(n) => {
                assert!(*self.slots_used() >= 2 * n);
                self.a.const_add(ADD, P64, RSP, RSP, (n * 16) as u64);
                *self.slots_used() -= 2 * n;
            },
            Action::Debug(x) => {
                for rs in CALLER_SAVES.chunks(2).rev() {
                    self.a.push(rs[0], rs[1]);
                }
                let x = self.src_to_register(x, ARGUMENTS[0]);
                self.move_(ARGUMENTS[0], x);
                self.const_(TEMP0, debug_word as *const () as u64);
                self.a.call(TEMP0);
                for rs in CALLER_SAVES.chunks(2) {
                    self.a.pop(rs[0], rs[1]);
                }
            },
        };
    }

    fn count(&mut self, counter: Counter) {
        self.mem(LDR, TEMP0, self.counter_address(counter), TEMP1);
        self.a.const_add(ADD, P64, TEMP0, TEMP0, 1);
        self.mem(STR, TEMP0, self.counter_address(counter), TEMP1);
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
    use super::*;
    use super::super::assembler::tests::{disassemble};
    use super::super::Condition::EQ;
    use super::super::super::{Lower as _};

    const LABEL: usize = 0x00024680;

    #[test]
    fn allocatable_regs() {
        for &r in &ALLOCATABLE_REGISTERS {
            assert_ne!(r, POOL);
            assert_ne!(r, TEMP0);
            assert_ne!(r, TEMP1);
        }
    }

    /** Test that we can patch jumps and calls. */
    #[test]
    fn steal() {
        let pool = Pool::new(0);
        let mut lo = Lowerer::<Vec<u8>>::new(pool);
        let start = lo.here().target().unwrap();
        let mut label = Label::new(None);
        lo.jump_if(EQ, &mut label);
        lo.const_jump(&mut label);
        lo.const_call(&mut label);
        disassemble(&lo.a, start, vec![
            "b.eq 0xfffffffffff00000",
            "b 0xfffffffff8000004",
            "bl 0xfffffffff8000008",
        ]).unwrap();
        let mut new_label = Label::new(Some(LABEL));
        lo.steal(&mut label, &mut new_label);
        label = new_label;
        disassemble(&lo.a, start, vec![
            "b.eq 0x24680",
            "b 0x24680",
            "bl 0x24680",
        ]).unwrap();
        let mut new_label = Label::new(Some(LABEL));
        lo.steal(&mut label, &mut new_label);
        disassemble(&lo.a, start, vec![
            "b.eq 0x24680",
            "b 0x24680",
            "bl 0x24680",
        ]).unwrap();
    }
}
