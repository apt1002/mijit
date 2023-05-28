//! A partial implementation of the [Beetle] virtual machine in Mijit.
//! This serves as an illustrative example as an integration test.
//!
//! [Beetle]: https://github.com/rrthomas/beetle

use memoffset::{offset_of};

use super::code::{
    UnaryOp, BinaryOp, Width, Register, REGISTERS, GLOBAL, EBB, Marshal,
    build, build_block, Builder,
};
use UnaryOp::*;
use BinaryOp::*;
use Width::*;
use super::target::{Word, Target};
use super::jit::{EntryId, Jit};

mod registers;
pub use registers::{Registers, M0Registers};

/// The number of bytes in a cell.
pub const CELL: i32 = 4;

/// The number of bits in a word.
pub const CELL_BITS: i32 = CELL * 8;

//-----------------------------------------------------------------------------

const R1: Register = REGISTERS[1];
const R2: Register = REGISTERS[2];
const R3: Register = REGISTERS[3];
const BEP: Register = REGISTERS[4];
const BI: Register = REGISTERS[5];
const BA: Register = REGISTERS[6];
const BSP: Register = REGISTERS[7];
const BRP: Register = REGISTERS[8];
const M0: Register = REGISTERS[9];
const REGS: Register = REGISTERS[10];

/// Returns the address of `Registers.$field`.
macro_rules! register {
    ($field: ident) => {
        (REGS, offset_of!(Registers, $field) as i32 + 8, Four)
    }
}

/// The return code used to indicate normal exit from the hot code.
const NOT_IMPLEMENTED: i64 = 0;
/// Dummy return code which should never actually occur.
const UNDEFINED: i64 = i64::MAX;

//-----------------------------------------------------------------------------

/// Computes into `BI` the native address corresponding to `addr`.
fn native_address(b: &mut Builder<EntryId>, addr: Register) {
    b.binary64(Add, BI, M0, addr);
}

/// Loads `dest` from `addr`. `BI` is corrupted.
fn load(b: &mut Builder<EntryId>, dest: Register, addr: Register) {
    native_address(b, addr);
    b.load(dest, (BI, 0, Four));
    b.send(M0, BI);
}

/// Stores `dest` at `addr`. `BI` is corrupted.
fn store(b: &mut Builder<EntryId>, src: Register, addr: Register) {
    native_address(b, addr);
    b.store(src, (BI, 0, Four));
    b.send(M0, BI);
}

/// Pops `dest` from the stack at `sp`. `BI` is corrupted.
fn pop(b: &mut Builder<EntryId>, dest: Register, sp: Register) {
    load(b, dest, sp);
    b.const_binary32(Add, sp, sp, CELL);
}

/// Pushes `src` to the stack at `sp`. `BI` is corrupted.
fn push(b: &mut Builder<EntryId>, src: Register, sp: Register) {
    b.const_binary32(Sub, sp, sp, CELL);
    store(b, src, sp);
}

/// The performance-critical part of the virtual machine.
#[derive(Debug)]
pub struct Beetle<T: Target> {
    pub jit: Jit<T>,
    pub root: EntryId,
}

impl<T: Target> Beetle<T> {
    #[allow(clippy::too_many_lines)]
    pub fn new(target: T) -> Self {
        let mut jit = Jit::new(target);
        let marshal = Marshal {
            prologue: build_block(|b| {
                b.move_(REGS, GLOBAL);
                b.load(BEP, register!(ep));
                b.load(BI, register!(i));
                b.load(BA, register!(a));
                b.load(BSP, register!(sp));
                b.load(BRP, register!(rp));
                b.load(M0, (REGS, 0, Eight));
            }),
            epilogue: build_block(|b| {
                b.store(BEP, register!(ep));
                b.store(BI, register!(i));
                b.store(BA, register!(a));
                b.store(BSP, register!(sp));
                b.store(BRP, register!(rp));
                // No need to save `M0`, but we must use it. Dummy op.
                b.send(REGS, M0);
                b.move_(GLOBAL, REGS);
            }),
        };
        let root = jit.new_entry(&marshal, UNDEFINED);

        // Immediate branch.
        let branchi = jit.new_entry(&marshal, UNDEFINED);
        jit.define(branchi, &build(|mut b| {
            b.const_binary32(Mul, R1, BA, CELL);
            b.binary32(Add, BEP, BEP, R1);
            pop(&mut b, BA, BEP);
            b.jump(root)
        }));

        // Not implemented.
        let not_implemented2 = jit.new_entry(&marshal, NOT_IMPLEMENTED);
        let not_implemented = jit.new_entry(&marshal, UNDEFINED);
        jit.define(not_implemented, &build(|mut b| {
            b.const_binary32(Lsl, BA, BA, 8);
            b.binary32(Or, BA, BA, BI);
            b.jump(not_implemented2)
        }));

        // Op-code dispatch routines.
        let mut actions: Box<[EBB<EntryId>]> = (0..0x63).map(|_| {
            build(|b| b.jump(not_implemented))
        }).collect();

        // NEXT
        actions[0x00] = build(|mut b| {
            pop(&mut b, BA, BEP);
            b.jump(root)
        });

        // DUP
        actions[0x01] = build(|mut b| {
            load(&mut b, R2, BSP);
            push(&mut b, R2, BSP);
            b.jump(root)
        });

        // DROP
        actions[0x02] = build(|mut b| {
            b.const_binary32(Add, BSP, BSP, CELL);
            b.jump(root)
        });

        // SWAP
        actions[0x03] = build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            store(&mut b, R2, BSP);
            push(&mut b, R3, BSP);
            b.jump(root)
        });

        // OVER
        actions[0x04] = build(|mut b| {
            b.const_binary32(Add, R1, BSP, CELL);
            load(&mut b, R2, R1);
            push(&mut b, R2, BSP);
            b.jump(root)
        });

        // ROT
        actions[0x05] = build(|mut b| {
            load(&mut b, R2, BSP);
            b.const_binary32(Add, R1, BSP, CELL);
            load(&mut b, R3, R1);
            store(&mut b, R2, R1);
            b.const_binary32(Add, R1, BSP, 2 * CELL);
            load(&mut b, R2, R1);
            store(&mut b, R3, R1);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // -ROT
        actions[0x06] = build(|mut b| {
            load(&mut b, R2, BSP);
            b.const_binary32(Add, R1, BSP, 2 * CELL);
            load(&mut b, R3, R1);
            store(&mut b, R2, R1);
            b.const_binary32(Add, R1, BSP, CELL);
            load(&mut b, R2, R1);
            store(&mut b, R3, R1);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // TUCK
        actions[0x07] = build(|mut b| {
            load(&mut b, R2, BSP);
            b.const_binary32(Add, R1, BSP, CELL);
            load(&mut b, R3, R1);
            store(&mut b, R2, R1);
            store(&mut b, R3, BSP);
            push(&mut b, R2, BSP);
            b.jump(root)
        });

        // NIP
        actions[0x08] = build(|mut b| {
            pop(&mut b, R2, BSP);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // <
        actions[0x0F] = build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            b.binary32(Lt, R2, R3, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // >
        actions[0x10] = build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            b.binary32(Lt, R2, R2, R3);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // =
        actions[0x11] = build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            b.binary32(Eq, R2, R3, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // <>
        actions[0x12] = build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            b.binary32(Eq, R2, R3, R2);
            b.unary32(Not, R2, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // 0<
        actions[0x13] = build(|mut b| {
            load(&mut b, R2, BSP);
            b.const_binary32(Lt, R2, R2, 0);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // 0>
        actions[0x14] = build(|mut b| {
            load(&mut b, R2, BSP);
            b.const_(R3, 0);
            b.binary32(Lt, R2, R3, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // 0=
        actions[0x15] = build(|mut b| {
            load(&mut b, R2, BSP);
            b.const_binary32(Eq, R2, R2, 0);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // 0<>
        actions[0x16] = build(|mut b| {
            load(&mut b, R2, BSP);
            b.const_binary32(Eq, R2, R2, 0);
            b.unary32(Not, R2, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // U<
        actions[0x17] = build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            b.binary32(Ult, R2, R3, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // U>
        actions[0x18] = build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            b.binary32(Ult, R2, R2, R3);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // 0
        actions[0x19] = build(|mut b| {
            b.const_(R2, 0);
            push(&mut b, R2, BSP);
            b.jump(root)
        });

        // 1
        actions[0x1A] = build(|mut b| {
            b.const_(R2, 1);
            push(&mut b, R2, BSP);
            b.jump(root)
        });

        // -1
        actions[0x1B] = build(|mut b| {
            b.const_(R2, -1i32 as u32 as i64);
            push(&mut b, R2, BSP);
            b.jump(root)
        });

        // +
        actions[0x1E] = build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            b.binary32(Add, R2, R3, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // -
        actions[0x1F] = build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            b.binary32(Sub, R2, R3, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // >-<
        actions[0x20] = build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            b.binary32(Sub, R2, R2, R3);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // 1+
        actions[0x21] = build(|mut b| {
            load(&mut b, R2, BSP);
            b.const_binary32(Add, R2, R2, 1);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // 1-
        actions[0x22] = build(|mut b| {
            load(&mut b, R2, BSP);
            b.const_binary32(Sub, R2, R2, 1);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // *
        actions[0x25] = build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            b.binary32(Mul, R2, R3, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // ABS
        actions[0x2D] = build(|mut b| {
            load(&mut b, R2, BSP);
            b.unary32(Abs, R2, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // NEGATE
        actions[0x2E] = build(|mut b| {
            load(&mut b, R2, BSP);
            b.unary32(Negate, R2, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // MAX
        actions[0x2F] = build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            b.binary32(Max, R2, R3, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        actions[0x30] = // MIN
        build(|mut b| {
            pop(&mut b, R2, BSP);
            load(&mut b, R3, BSP);
            b.binary32(Min, R2, R3, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        actions[0x31] = // INVERT
        build(|mut b| {
            load(&mut b, R2, BSP);
            b.unary32(Not, R2, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // @
        actions[0x39] = build(|mut b| {
            load(&mut b, R2, BSP);
            load(&mut b, R2, R2);
            store(&mut b, R2, BSP);
            b.jump(root)
        });

        // !
        actions[0x3A] = build(|mut b| {
            pop(&mut b, R2, BSP);
            pop(&mut b, R3, BSP);
            store(&mut b, R3, R2);
            b.jump(root)
        });

        // +!
        actions[0x3D] = build(|mut b| {
            pop(&mut b, R2, BSP);
            pop(&mut b, R3, BSP);
            load(&mut b, R1, R2);
            b.binary32(Add, R3, R1, R3);
            store(&mut b, R3, R2);
            b.jump(root)
        });

        // BRANCHI
        actions[0x43] = build(|b| { b.jump(branchi) });

        // ?BRANCHI
        actions[0x45] = build(|mut b| {
            pop(&mut b, BI, BSP);
            b.if_(BI,
                build(|mut b| {
                    pop(&mut b, BA, BEP);
                    b.jump(root)
                }),
                build(|b| { b.jump(branchi) }),
            )
        });

        // CALLI
        actions[0x49] = build(|mut b| {
            push(&mut b, BEP, BRP);
            b.jump(branchi)
        });

        // EXIT
        actions[0x4A] = build(|mut b| {
            pop(&mut b, BEP, BRP);
            pop(&mut b, BA, BEP);
            b.jump(root)
        });

        // (LITERAL)I
        actions[0x53] = build(|mut b| {
            push(&mut b, BA, BSP);
            pop(&mut b, BA, BEP);
            b.jump(root)
        });

        // Main dispatch loop.
        jit.define(root, &build(|mut b| {
            b.const_binary32(And, BI, BA, 0xFF);
            b.const_binary32(Asr, BA, BA, 8);
            b.index(BI, actions, build(|b| b.jump(not_implemented)))
        }));

        Self {jit, root}
    }

    /// # Safety
    ///
    /// There is no memory bounds checking in this implementation of Beetle.
    pub unsafe fn run(&mut self, registers: &mut M0Registers) {
        let result = self.jit.run(self.root, registers);
        assert_eq!(result, Word {s: NOT_IMPLEMENTED});
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests;
