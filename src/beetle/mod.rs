/*!
 * A partial implementation of the [Beetle] virtual machine in Mijit.
 * This serves as an illustrative example as an integration test.
 *
 * [Beetle]: https://github.com/rrthomas/beetle
 */

use super::code::{self, UnaryOp, BinaryOp, Register, REGISTERS, Global, Switch, Ending};
use UnaryOp::*;
use BinaryOp::*;
use super::target::{Word, Target};
use super::jit::{EntryId, Jit2};

mod registers;
pub use registers::{Registers};

/** The number of bytes in a cell. */
pub const CELL: u32 = 4;

/** The number of bits in a word. */
pub const CELL_BITS: u32 = CELL * 8;

//-----------------------------------------------------------------------------

const TEMP: Register = REGISTERS[0];
const R1: Register = REGISTERS[1];
const R2: Register = REGISTERS[2];
const R3: Register = REGISTERS[3];
const BEP: Register = REGISTERS[4];
const BI: Register = REGISTERS[5];
const BA: Register = REGISTERS[6];
const BSP: Register = REGISTERS[7];
const BRP: Register = REGISTERS[8];
const M0: Register = REGISTERS[9];

mod builder;
use builder::{build, marshal};

/** The return code used to indicate normal exit from the hot code. */
const NOT_IMPLEMENTED: i64 = 0;
/** Dummy return code which should never actually occur. */
const UNDEFINED: i64 = i64::MAX;

//-----------------------------------------------------------------------------

/** The performance-critical part of the virtual machine. */
#[derive(Debug)]
pub struct Beetle<T: Target> {
    pub jit: Jit2<T>,
    pub root: EntryId,
}

impl<T: Target> Beetle<T> {
    #[allow(clippy::too_many_lines)]
    pub fn new(target: T) -> Self {
        let mut jit = Jit2::new(target, 2);
        let root = jit.new_entry(&marshal(vec![BI]), UNDEFINED);

        // Immediate branch.
        let branchi = jit.new_entry(&marshal(vec![BI]), UNDEFINED);
        jit.define(branchi, &build(|b| {
            b.const_binary(Mul, R1, BA, CELL);
            b.binary(Add, BEP, BEP, R1);
            b.pop(BA, BEP);
        }, Ending::Leaf(root)));
        
        // Not implemented.
        let not_implemented2 = jit.new_entry(&marshal(vec![]), NOT_IMPLEMENTED);
        let not_implemented = jit.new_entry(&marshal(vec![]), UNDEFINED);
        jit.define(not_implemented, &build(|b| {
            b.const_binary(Lsl, BA, BA, 8);
            b.binary(Or, BA, BA, BI);
        }, Ending::Leaf(not_implemented2)));

        // Main dispatch loop.
        jit.define(root, &build(|b| {
            b.const_binary(And, BI, BA, 0xFF);
            b.const_binary(Asr, BA, BA, 8);
        }, Ending::Switch(Switch::new(
            BI.into(),
            Box::new([
                // NEXT
                build(|b| {
                    b.pop(BA, BEP);
                }, Ending::Leaf(root)),

                // DUP
                build(|b| {
                    b.load(R2, BSP);
                    b.push(R2, BSP);
                }, Ending::Leaf(root)),

                // DROP
                build(|b| {
                    b.const_binary(Add, BSP, BSP, CELL);
                }, Ending::Leaf(root)),

                // SWAP
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.store(R2, BSP);
                    b.push(R3, BSP);
                }, Ending::Leaf(root)),

                // OVER
                build(|b| {
                    b.const_binary(Add, R1, BSP, CELL);
                    b.load(R2, R1);
                    b.push(R2, BSP);
                }, Ending::Leaf(root)),

                // ROT
                build(|b| {
                    b.load(R2, BSP);
                    b.const_binary(Add, R1, BSP, CELL);
                    b.load(R3, R1);
                    b.store(R2, R1);
                    b.const_binary(Add, R1, BSP, 2 * CELL);
                    b.load(R2, R1);
                    b.store(R3, R1);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // -ROT
                build(|b| {
                    b.load(R2, BSP);
                    b.const_binary(Add, R1, BSP, 2 * CELL);
                    b.load(R3, R1);
                    b.store(R2, R1);
                    b.const_binary(Add, R1, BSP, CELL);
                    b.load(R2, R1);
                    b.store(R3, R1);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // TUCK
                build(|b| {
                    b.load(R2, BSP);
                    b.const_binary(Add, R1, BSP, CELL);
                    b.load(R3, R1);
                    b.store(R2, R1);
                    b.store(R3, BSP);
                    b.push(R2, BSP);
                }, Ending::Leaf(root)),

                // NIP
                build(|b| {
                    b.pop(R2, BSP);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // PICK
                build(|_| {}, Ending::Leaf(not_implemented)),

                // ROLL
                build(|_| {}, Ending::Leaf(not_implemented)),

                // ?DUP
                build(|_| {}, Ending::Leaf(not_implemented)),

                // >R
                build(|_| {}, Ending::Leaf(not_implemented)),

                // R>
                build(|_| {}, Ending::Leaf(not_implemented)),

                // R@
                build(|_| {}, Ending::Leaf(not_implemented)),

                // <
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.binary(Lt, R2, R3, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // >
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.binary(Lt, R2, R2, R3);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // =
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.binary(Eq, R2, R3, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // <>
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.binary(Eq, R2, R3, R2);
                    b.unary(Not, R2, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // 0<
                build(|b| {
                    b.load(R2, BSP);
                    b.const_binary(Lt, R2, R2, 0);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // 0>
                build(|b| {
                    b.load(R2, BSP);
                    b.const_(R3, 0);
                    b.binary(Lt, R2, R3, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // 0=
                build(|b| {
                    b.load(R2, BSP);
                    b.const_binary(Eq, R2, R2, 0);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // 0<>
                build(|b| {
                    b.load(R2, BSP);
                    b.const_binary(Eq, R2, R2, 0);
                    b.unary(Not, R2, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // U<
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.binary(Ult, R2, R3, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // U>
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.binary(Ult, R2, R2, R3);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // 0
                build(|b| {
                    b.const_(R2, 0);
                    b.push(R2, BSP);
                }, Ending::Leaf(root)),

                // 1
                build(|b| {
                    b.const_(R2, 1);
                    b.push(R2, BSP);
                }, Ending::Leaf(root)),

                // -1
                build(|b| {
                    b.const_(R2, -1i32 as u32);
                    b.push(R2, BSP);
                }, Ending::Leaf(root)),

                // CELL
                build(|_| {}, Ending::Leaf(not_implemented)),

                // -CELL
                build(|_| {}, Ending::Leaf(not_implemented)),

                // +
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.binary(Add, R2, R3, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // -
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.binary(Sub, R2, R3, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // >-<
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.binary(Sub, R2, R2, R3);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // 1+
                build(|b| {
                    b.load(R2, BSP);
                    b.const_binary(Add, R2, R2, 1);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // 1-
                build(|b| {
                    b.load(R2, BSP);
                    b.const_binary(Sub, R2, R2, 1);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // CELL+
                build(|_| {}, Ending::Leaf(not_implemented)),

                // CELL-
                build(|_| {}, Ending::Leaf(not_implemented)),

                // *
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.binary(Mul, R2, R3, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // /
                build(|_| {}, Ending::Leaf(not_implemented)),

                // MOD
                build(|_| {}, Ending::Leaf(not_implemented)),

                // /MOD
                build(|_| {}, Ending::Leaf(not_implemented)),

                // U/MOD
                build(|_| {}, Ending::Leaf(not_implemented)),

                // S/REM
                build(|_| {}, Ending::Leaf(not_implemented)),

                // 2/
                build(|_| {}, Ending::Leaf(not_implemented)),

                // CELLS
                build(|_| {}, Ending::Leaf(not_implemented)),

                // ABS
                build(|b| {
                    b.load(R2, BSP);
                    b.unary(Abs, R2, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // NEGATE
                build(|b| {
                    b.load(R2, BSP);
                    b.unary(Negate, R2, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // MAX
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.binary(Max, R2, R3, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // MIN
                build(|b| {
                    b.pop(R2, BSP);
                    b.load(R3, BSP);
                    b.binary(Min, R2, R3, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // INVERT
                build(|b| {
                    b.load(R2, BSP);
                    b.unary(Not, R2, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // AND
                build(|_| {}, Ending::Leaf(not_implemented)),

                // OR
                build(|_| {}, Ending::Leaf(not_implemented)),

                // XOR
                build(|_| {}, Ending::Leaf(not_implemented)),

                // LSHIFT
                build(|_| {}, Ending::Leaf(not_implemented)),

                // RSHIFT
                build(|_| {}, Ending::Leaf(not_implemented)),

                // 1LSHIFT
                build(|_| {}, Ending::Leaf(not_implemented)),

                // 1RSHIFT
                build(|_| {}, Ending::Leaf(not_implemented)),

                // @
                build(|b| {
                    b.load(R2, BSP);
                    b.load(R2, R2);
                    b.store(R2, BSP);
                }, Ending::Leaf(root)),

                // !
                build(|b| {
                    b.pop(R2, BSP);
                    b.pop(R3, BSP);
                    b.store(R3, R2);
                }, Ending::Leaf(root)),

                // C@
                build(|_| {}, Ending::Leaf(not_implemented)),

                // C!
                build(|_| {}, Ending::Leaf(not_implemented)),

                // +!
                build(|b| {
                    b.pop(R2, BSP);
                    b.pop(R3, BSP);
                    b.load(R1, R2);
                    b.binary(Add, R3, R1, R3);
                    b.store(R3, R2);
                }, Ending::Leaf(root)),

                // SP@
                build(|_| {}, Ending::Leaf(not_implemented)),

                // SP!
                build(|_| {}, Ending::Leaf(not_implemented)),

                // RP@
                build(|_| {}, Ending::Leaf(not_implemented)),

                // RP!
                build(|_| {}, Ending::Leaf(not_implemented)),

                // BRANCH
                build(|_| {}, Ending::Leaf(not_implemented)),

                // BRANCHI
                build(|_| {}, Ending::Leaf(branchi)),

                // ?BRANCH
                build(|_| {}, Ending::Leaf(not_implemented)),

                // ?BRANCHI
                build(|b| {
                    b.pop(BI, BSP);
                }, Ending::Switch(Switch::if_(
                    BI.into(),
                    build(|b| {
                        b.pop(BA, BEP);
                    }, Ending::Leaf(root)),
                    build(|_| {}, Ending::Leaf(branchi)),
                ))),

                // EXECUTE
                build(|_| {}, Ending::Leaf(not_implemented)),

                // @EXECUTE
                build(|_| {}, Ending::Leaf(not_implemented)),

                // CALL
                build(|_| {}, Ending::Leaf(not_implemented)),

                // CALLI
                build(|b| {
                    b.push(BEP, BRP);
                }, Ending::Leaf(branchi)),

                // EXIT
                build(|b| {
                    b.pop(BEP, BRP);
                    b.pop(BA, BEP);
                }, Ending::Leaf(root)),

                // (DO)
                build(|_| {}, Ending::Leaf(not_implemented)),

                // (LOOP)
                build(|_| {}, Ending::Leaf(not_implemented)),

                // (LOOP)I
                build(|_| {}, Ending::Leaf(not_implemented)),

                // (+LOOP)
                build(|_| {}, Ending::Leaf(not_implemented)),

                // (+LOOP)I
                build(|_| {}, Ending::Leaf(not_implemented)),

                // UNLOOP
                build(|_| {}, Ending::Leaf(not_implemented)),

                // J
                build(|_| {}, Ending::Leaf(not_implemented)),

                // (LITERAL)
                build(|_| {}, Ending::Leaf(not_implemented)),

                // (LITERAL)I
                build(|b| {
                    b.push(BA, BSP);
                    b.pop(BA, BEP);
                }, Ending::Leaf(root)),
            ]),
            build(|_| {}, Ending::Leaf(not_implemented)),
        ))));

        Self {jit, root}
    }

    pub fn global_mut(&mut self, global: Global) -> &mut Word {
        self.jit.global_mut(global)
    }

    pub unsafe fn run(mut self, registers: &mut Registers, m0: &mut[u32]) -> std::io::Result<Self> {
        *self.jit.global_mut(Global(0)) = Word {mp: (registers as *mut Registers).cast()};
        *self.jit.global_mut(Global(1)) = Word {mp: (m0.as_mut_ptr()).cast()};
        let (jit, result) = self.jit.run(self.root)?;
        assert_eq!(result, Word {s: NOT_IMPLEMENTED});
        self.jit = jit;
        Ok(self)
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests;
