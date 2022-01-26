/*!
 * A partial implementation of the [Beetle] virtual machine in Mijit.
 * This serves as an illustrative example as an integration test.
 *
 * [Beetle]: https://github.com/rrthomas/beetle
 */

use memoffset::{offset_of};
use super::code::{
    self, UnaryOp, BinaryOp, Global, Register, REGISTERS, Variable,
    Switch, Case, Convention, Marshal,
};
use UnaryOp::*;
use BinaryOp::*;

mod registers;
pub use registers::{Registers};

/** The number of bytes in a cell. */
pub const CELL: u32 = 4;

/** The number of bits in a word. */
pub const CELL_BITS: u32 = CELL * 8;

//-----------------------------------------------------------------------------

/* Register allocation. */

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

//-----------------------------------------------------------------------------

/* Control-flow states. */

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum State {
    Root,
    Dispatch,
    Branchi,
    Qbranchi,
    NotImplemented,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NotImplemented;

//-----------------------------------------------------------------------------

mod builder;
use builder::{build, Builder};

/** Returns the offset of `$field`. */
macro_rules! register {
    ($field: ident) => {
        offset_of!(Registers, $field)
    }
}

/** The performance-critical part of the virtual machine. */
#[derive(Debug)]
pub struct Machine;

impl code::Machine for Machine {
    type State = State;

    type Trap = NotImplemented;

    fn num_globals(&self) -> usize { 2 }

    fn marshal(&self, state: Self::State) -> Marshal {
        let mut live_values = vec![Global(0).into(), BEP.into(), BSP.into(), BRP.into(), M0.into()];
        #[allow(clippy::match_same_arms)]
        live_values.extend(match state {
            State::Root => vec![BA],
            State::Branchi => vec![BA],
            State::Qbranchi => vec![BA, BI],
            State::Dispatch => vec![BA, BI],
            State::NotImplemented => vec![BA, BI],
        }.into_iter().map(Variable::Register));
        let prologue = {
            let mut b = Builder::new();
            b.load_register(BEP, register!(ep));
            b.load_register(BI, register!(i));
            b.load_register(BA, register!(a));
            b.load_register(BSP, register!(sp));
            b.load_register(BRP, register!(rp));
            b.load_global(M0, Global(1));
            b.finish()
        };
        let epilogue = {
            let mut b = Builder::new();
            for v in [BA, BI] {
                if !live_values.contains(&v.into()) {
                    b.const64(v, 0xDEADDEADDEADDEADu64);
                }
            }
            b.store_register(BEP, register!(ep));
            b.store_register(BI, register!(i));
            b.store_register(BA, register!(a));
            b.store_register(BSP, register!(sp));
            b.store_register(BRP, register!(rp));
            b.store_global(M0, Global(1));
            b.finish()
        };
        let convention = Convention {
            slots_used: 0,
            live_values: live_values.into(),
        };
        Marshal {prologue, convention, epilogue}
    }

    #[allow(clippy::too_many_lines)]
    fn code(&self, state: Self::State) -> Switch<Case<Result<Self::State, Self::Trap>>> {
        match state {
            State::Root => Switch::always(build(|b| {
                b.const_binary(And, BI, BA, 0xFF);
                b.const_binary(Asr, BA, BA, 8);
            }, Ok(State::Dispatch))),
            State::Branchi => Switch::always(build(|b| {
                b.const_binary(Mul, R1, BA, CELL);
                b.binary(Add, BEP, BEP, R1);
                b.pop(BA, BEP);
            }, Ok(State::Root))),
            State::Qbranchi => Switch::if_(
                BI.into(), // Top of stack.
                build(|b| {
                    b.pop(BA, BEP);
                }, Ok(State::Root)),
                build(|_| {}, Ok(State::Branchi)),
            ),
            State::NotImplemented => Switch::always(build(|b| {
                b.const_binary(Lsl, BA, BA, 8);
                b.binary(Or, BA, BA, BI);
            }, Err(NotImplemented))),
            State::Dispatch => Switch::new(
                BI.into(),
                Box::new([
                    // NEXT
                    build(|b| {
                        b.pop(BA, BEP);
                    }, Ok(State::Root)),

                    // DUP
                    build(|b| {
                        b.load(R2, BSP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // DROP
                    build(|b| {
                        b.const_binary(Add, BSP, BSP, CELL);
                    }, Ok(State::Root)),

                    // SWAP
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.store(R2, BSP);
                        b.push(R3, BSP);
                    }, Ok(State::Root)),

                    // OVER
                    build(|b| {
                        b.const_binary(Add, R1, BSP, CELL);
                        b.load(R2, R1);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

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
                    }, Ok(State::Root)),

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
                    }, Ok(State::Root)),

                    // TUCK
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R1, BSP, CELL);
                        b.load(R3, R1);
                        b.store(R2, R1);
                        b.store(R3, BSP);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // NIP
                    build(|b| {
                        b.pop(R2, BSP);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // PICK
                    build(|_| {}, Ok(State::NotImplemented)),

                    // ROLL
                    build(|_| {}, Ok(State::NotImplemented)),

                    // ?DUP
                    build(|_| {}, Ok(State::NotImplemented)),

                    // >R
                    build(|_| {}, Ok(State::NotImplemented)),

                    // R>
                    build(|_| {}, Ok(State::NotImplemented)),

                    // R@
                    build(|_| {}, Ok(State::NotImplemented)),

                    // <
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Lt, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // >
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Lt, R2, R2, R3);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // =
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Eq, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // <>
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Eq, R2, R3, R2);
                        b.unary(Not, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0<
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Lt, R2, R2, 0);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0>
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_(R3, 0);
                        b.binary(Lt, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0=
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Eq, R2, R2, 0);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0<>
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Eq, R2, R2, 0);
                        b.unary(Not, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // U<
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Ult, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // U>
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Ult, R2, R2, R3);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 0
                    build(|b| {
                        b.const_(R2, 0);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // 1
                    build(|b| {
                        b.const_(R2, 1);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // -1
                    build(|b| {
                        b.const_(R2, -1i32 as u32);
                        b.push(R2, BSP);
                    }, Ok(State::Root)),

                    // CELL
                    build(|_| {}, Ok(State::NotImplemented)),

                    // -CELL
                    build(|_| {}, Ok(State::NotImplemented)),

                    // +
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Add, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // -
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Sub, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // >-<
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Sub, R2, R2, R3);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 1+
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Add, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // 1-
                    build(|b| {
                        b.load(R2, BSP);
                        b.const_binary(Sub, R2, R2, 1);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // CELL+
                    build(|_| {}, Ok(State::NotImplemented)),

                    // CELL-
                    build(|_| {}, Ok(State::NotImplemented)),

                    // *
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Mul, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // /
                    build(|_| {}, Ok(State::NotImplemented)),

                    // MOD
                    build(|_| {}, Ok(State::NotImplemented)),

                    // /MOD
                    build(|_| {}, Ok(State::NotImplemented)),

                    // U/MOD
                    build(|_| {}, Ok(State::NotImplemented)),

                    // S/REM
                    build(|_| {}, Ok(State::NotImplemented)),

                    // 2/
                    build(|_| {}, Ok(State::NotImplemented)),

                    // CELLS
                    build(|_| {}, Ok(State::NotImplemented)),

                    // ABS
                    build(|b| {
                        b.load(R2, BSP);
                        b.unary(Abs, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // NEGATE
                    build(|b| {
                        b.load(R2, BSP);
                        b.unary(Negate, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // MAX
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Max, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // MIN
                    build(|b| {
                        b.pop(R2, BSP);
                        b.load(R3, BSP);
                        b.binary(Min, R2, R3, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // INVERT
                    build(|b| {
                        b.load(R2, BSP);
                        b.unary(Not, R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // AND
                    build(|_| {}, Ok(State::NotImplemented)),

                    // OR
                    build(|_| {}, Ok(State::NotImplemented)),

                    // XOR
                    build(|_| {}, Ok(State::NotImplemented)),

                    // LSHIFT
                    build(|_| {}, Ok(State::NotImplemented)),

                    // RSHIFT
                    build(|_| {}, Ok(State::NotImplemented)),

                    // 1LSHIFT
                    build(|_| {}, Ok(State::NotImplemented)),

                    // 1RSHIFT
                    build(|_| {}, Ok(State::NotImplemented)),

                    // @
                    build(|b| {
                        b.load(R2, BSP);
                        b.load(R2, R2);
                        b.store(R2, BSP);
                    }, Ok(State::Root)),

                    // !
                    build(|b| {
                        b.pop(R2, BSP);
                        b.pop(R3, BSP);
                        b.store(R3, R2);
                    }, Ok(State::Root)),

                    // C@
                    build(|_| {}, Ok(State::NotImplemented)),

                    // C!
                    build(|_| {}, Ok(State::NotImplemented)),

                    // +!
                    build(|b| {
                        b.pop(R2, BSP);
                        b.pop(R3, BSP);
                        b.load(R1, R2);
                        b.binary(Add, R3, R1, R3);
                        b.store(R3, R2);
                    }, Ok(State::Root)),

                    // SP@
                    build(|_| {}, Ok(State::NotImplemented)),

                    // SP!
                    build(|_| {}, Ok(State::NotImplemented)),

                    // RP@
                    build(|_| {}, Ok(State::NotImplemented)),

                    // RP!
                    build(|_| {}, Ok(State::NotImplemented)),

                    // BRANCH
                    build(|_| {}, Ok(State::NotImplemented)),

                    // BRANCHI
                    build(|_| {}, Ok(State::Branchi)),

                    // ?BRANCH
                    build(|_| {}, Ok(State::NotImplemented)),

                    // ?BRANCHI
                    build(|b| {
                        b.pop(BI, BSP);
                    }, Ok(State::Qbranchi)),

                    // EXECUTE
                    build(|_| {}, Ok(State::NotImplemented)),

                    // @EXECUTE
                    build(|_| {}, Ok(State::NotImplemented)),

                    // CALL
                    build(|_| {}, Ok(State::NotImplemented)),

                    // CALLI
                    build(|b| {
                        b.push(BEP, BRP);
                    }, Ok(State::Branchi)),

                    // EXIT
                    build(|b| {
                        b.pop(BEP, BRP);
                        b.pop(BA, BEP);
                    }, Ok(State::Root)),

                    // (DO)
                    build(|_| {}, Ok(State::NotImplemented)),

                    // (LOOP)
                    build(|_| {}, Ok(State::NotImplemented)),

                    // (LOOP)I
                    build(|_| {}, Ok(State::NotImplemented)),

                    // (+LOOP)
                    build(|_| {}, Ok(State::NotImplemented)),

                    // (+LOOP)I
                    build(|_| {}, Ok(State::NotImplemented)),

                    // UNLOOP
                    build(|_| {}, Ok(State::NotImplemented)),

                    // J
                    build(|_| {}, Ok(State::NotImplemented)),

                    // (LITERAL)
                    build(|_| {}, Ok(State::NotImplemented)),

                    // (LITERAL)I
                    build(|b| {
                        b.push(BA, BSP);
                        b.pop(BA, BEP);
                    }, Ok(State::Root)),

                    // THROW
                    build(|_| {}, Ok(State::NotImplemented)),

                    // HALT
                    build(|_| {}, Ok(State::NotImplemented)),
                ]),
                build(|_| {}, Ok(State::NotImplemented)),
            ),
        }
    }

    fn initial_states(&self) -> Vec<Self::State> {
        vec![State::Root]
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests;
