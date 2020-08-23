use indexmap::{IndexSet};

use super::{code, x86_64};
use x86_64::*;
use code::{Action, TestOp, Machine, Precision};
use Register::*;
use Precision::*;
use BinaryOp::*;
use ShiftOp::*;


pub struct Lowerer<'a, M: Machine> {
    pub a: Assembler<'a>,
    pub machine: &'a M,
    pub globals: &'a IndexSet<M::Global>,
}

impl <'a, M: Machine> Lowerer<'a, M> {
    /** Returns the offset of `global` in the persistent data. */
    fn global_offset(&self, global: &M::Global) -> i32 {
        let index = self.globals.get_index_of(global).expect("Unknown global");
        (index * 8) as i32
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
                self.a.const_(prec, RC, mask as i64);
                self.a.op(And, prec, RC, discriminant);
                self.a.const_op(Cmp, prec, RC, value as i32);
                self.a.jump_if(Condition::Z, false, false_label);
            },
            TestOp::Lt(discriminant, value) => {
                self.a.const_op(Cmp, prec, discriminant, value as i32);
                self.a.jump_if(Condition::L, false, false_label);
            },
            TestOp::Ge(discriminant, value) => {
                self.a.const_op(Cmp, prec, discriminant, value as i32);
                self.a.jump_if(Condition::GE, false, false_label);
            },
            TestOp::Ult(discriminant, value) => {
                self.a.const_op(Cmp, prec, discriminant, value as i32);
                self.a.jump_if(Condition::B, false, false_label);
            },
            TestOp::Uge(discriminant, value) => {
                self.a.const_op(Cmp, prec, discriminant, value as i32);
                self.a.jump_if(Condition::AE, false, false_label);
            },
            TestOp::Eq(discriminant, value) => {
                self.a.const_op(Cmp, prec, discriminant, value as i32);
                self.a.jump_if(Condition::Z, false, false_label);
            },
            TestOp::Ne(discriminant, value) => {
                self.a.const_op(Cmp, prec, discriminant, value as i32);
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
        dest: code::R,
        src: code::R,
    ) {
        match unary_op {
            code::UnaryOp::Abs => {
                self.a.move_(prec, RC, src);
                self.a.const_(prec, dest, 0);
                self.a.op(Sub, prec, dest, RC);
                self.a.move_if(Condition::L, true, prec, dest, RC);
            },
            code::UnaryOp::Negate => {
                self.a.move_(prec, RC, src);
                self.a.const_(prec, dest, 0);
                self.a.op(Sub, prec, dest, RC);
            },
            code::UnaryOp::Not => {
                self.a.move_(prec, dest, src);
                self.a.const_op(Xor, prec, dest, -1);
            },
        };
    }

    /**
     * Assemble code to perform the given `binary_op`.
     */
    pub fn lower_binary_op(
        &mut self,
        binary_op: code::BinaryOp,
        prec: Precision,
        dest: code::R,
        src1: code::R,
        src2: code::R,
    ) {
        match binary_op {
            code::BinaryOp::Add => {
                self.a.move_(prec, dest, src1);
                self.a.op(Add, prec, dest, src2);
            },
            code::BinaryOp::Sub => {
                self.a.move_(prec, dest, src1);
                self.a.op(Sub, prec, dest, src2);
            },
            code::BinaryOp::Mul => {
                self.a.move_(prec, dest, src1);
                self.a.mul(prec, dest, src2);
            },
            // TODO: Define what happens when you shift too far.
            code::BinaryOp::Lsl => {
                self.a.move_(prec, dest, src1);
                self.a.move_(P32, RC, src2);
                self.a.shift(Shl, prec, dest);
            },
            code::BinaryOp::Lsr => {
                self.a.move_(prec, dest, src1);
                self.a.move_(P32, RC, src2);
                self.a.shift(Shr, prec, dest);
            },
            code::BinaryOp::Asr => {
                self.a.move_(prec, dest, src1);
                self.a.move_(P32, RC, src2);
                self.a.shift(Sar, prec, dest);
            },
            code::BinaryOp::And => {
                self.a.move_(prec, dest, src1);
                self.a.op(And, prec, dest, src2);
            },
            code::BinaryOp::Or => {
                self.a.move_(prec, dest, src1);
                self.a.op(Or, prec, dest, src2);
            },
            code::BinaryOp::Xor => {
                self.a.move_(prec, dest, src1);
                self.a.op(Xor, prec, dest, src2);
            },
            code::BinaryOp::Lt => {
                self.a.const_(prec, RC, 0);
                self.a.op(Cmp, prec, src1, src2);
                self.a.const_(prec, dest, -1);
                self.a.move_if(Condition::L, false, prec, dest, RC);
            },
            code::BinaryOp::Ult => {
                self.a.const_(prec, RC, 0);
                self.a.op(Cmp, prec, src1, src2);
                self.a.const_(prec, dest, -1);
                self.a.move_if(Condition::B, false, prec, dest, RC);
            },
            code::BinaryOp::Eq => {
                self.a.const_(prec, RC, 0);
                self.a.op(Cmp, prec, src1, src2);
                self.a.const_(prec, dest, -1);
                self.a.move_if(Condition::Z, false, prec, dest, RC);
            },
            code::BinaryOp::Max => {
                self.a.op(Cmp, prec, src1, src2);
                self.a.move_(prec, dest, src2);
                self.a.move_if(Condition::G, true, prec, dest, src1);
            },
            code::BinaryOp::Min => {
                self.a.op(Cmp, prec, src1, src2);
                self.a.move_(prec, dest, src2);
                self.a.move_if(Condition::L, true, prec, dest, src1);
            },
        };
    }

    fn lower_memory_location(mloc: code::MemoryLocation<M::Memory>) -> (code::R, x86_64::Width) {
        use code::MemoryLocation::*;
        match mloc {
            One(addr, _m) => (addr, x86_64::Width::U8),
            Two(addr, _m) => (addr, x86_64::Width::U16),
            Four(addr, _m) => (addr, x86_64::Width::U32),
            Eight(addr, _m) => (addr, x86_64::Width::U64),
        }
    }

    /**
     * Assemble code to perform the given `action`.
     */
    pub fn lower_action(
        &mut self,
        action: Action<M::Memory, M::Global>,
    ) {
        match action {
            Action::Constant(prec, dest, value) => {
                self.a.const_(prec, dest, value);
            },
            Action::Move(prec, dest, src) => {
                self.a.move_(prec, dest, src);
            },
            Action::Unary(op, prec, dest, src) => {
                self.lower_unary_op(op, prec, dest, src);
            },
            Action::Binary(op, prec, dest, src1, src2) => {
                self.lower_binary_op(op, prec, dest, src1, src2);
            },
            Action::Division(_op, _prec, _, _, _, _) => {
                panic!("FIXME: Don't know how to assemble div");
            },
            Action::LoadGlobal(dest, global) => {
                let offset = self.global_offset(&global);
                self.a.load(P64, dest, (R8, offset));
            },
            Action::StoreGlobal(src, global) => {
                let offset = self.global_offset(&global);
                self.a.store(P64, (R8, offset), src);
            },
            Action::Load(dest, mloc) => {
                let (addr, width) = Self::lower_memory_location(mloc);
                self.a.load_narrow(P64, width, dest, (addr, 0));
            },
            Action::Store(src, mloc) => {
                let (addr, width) = Self::lower_memory_location(mloc);
                self.a.store_narrow(width, (addr, 0), src);
            },
            Action::Push(src) => {
                self.a.push(src);
            },
            Action::Pop(dest) => {
                self.a.pop(dest);
            },
            Action::Debug(x) => {
                self.a.debug(x);
            },
        };
    }
}
