use super::{code, target, ebb, cost, Dataflow, Node, Out, Cold, CFT, Op, Resources};
use ebb::{EBB};

mod flood;
use flood::{flood};

mod keep_alive;
pub use keep_alive::{keep_alive_sets};

mod allocator;
pub use allocator::{Instruction, allocate};

mod moves;
pub use moves::{moves};

mod codegen;
pub use codegen::{generate_code};

//-----------------------------------------------------------------------------

use code::{Register};

const NUM_REGISTERS: usize = target::x86_64::ALLOCATABLE_REGISTERS.len();

fn all_registers() -> impl Iterator<Item=Register> {
    (0..NUM_REGISTERS).map(|i| Register::new(i as u8).unwrap())
}

//-----------------------------------------------------------------------------

pub fn build(
    _num_globals: usize,
    dataflow: &Dataflow,
    cft: &CFT,
) -> EBB {
    // Compute the keep-alive sets.
    let _hpt = keep_alive_sets(dataflow, cft);

    // TODO:
    // Make an initial [`Schedule`].
    // Choose the execution order and allocate [`Register`]s.
    // Generate the [`Action`]s.
    unimplemented!()
}
