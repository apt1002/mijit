use super::{Op, Resources};
pub use Op::*;

/**
 * The CPU resources available per cycle. The different resources are as
 * follows (modelled on Skylake):
 *  - The number of instructions decoded.
 *  - The number of flag-using macro instructions (this is a hack).
 *  - The number of address generation units.
 *  - The number of load units.
 *  - The number of store units.
 *  - The number of arithmetic / logic units.
 *  - The number of multiplication units.
 * These correspond to the hexadecimal digits of the [`Resources`] from least
 * to most significant.
 */
pub const BUDGET: Resources = Resources::new(0x1412316);

/** The resources needed to spill an Out. */
pub const SPILL_COST: Resources = Resources::new(0x0010101);

/** The additional resources needed per operand that is a Slot. */
pub const SLOT_COST: Resources = Resources::new(0x0001100);

//-----------------------------------------------------------------------------

/** Represents the cost of executing an [`Op`] (for example). */
#[derive(Debug)]
pub struct Cost {
    pub input_latencies: &'static [u8],
    pub output_latencies: &'static [u8],
    pub resources: Resources,
}

/** The resources needed to move a value from one `Register` to another. */
pub const MOVE_COST: Cost = Cost {
    input_latencies: &[0],
    output_latencies: &[0],
    resources: Resources::new(0x0000001),
};

/** The cost of a typical ALU operation such as `Constant`, `Add`. */
pub const ALU_COST: Cost = Cost {
    input_latencies: &[0, 0],
    output_latencies: &[1],
    resources: Resources::new(0x0100001),
};

/** The cost of a typical conditional operation such as `Abs`, `Max`. */
pub const CONDITIONAL_COST: Cost = Cost {
    input_latencies: &[0, 0],
    output_latencies: &[2],
    resources: Resources::new(0x0200013),
};

/** The cost of a typical ALU operation such as `Constant`, `Add`. */
pub const MUL_COST: Cost = Cost {
    input_latencies: &[0, 0],
    output_latencies: &[3],
    resources: Resources::new(0x1100001),
};

/** The cost of a typical shift operation such as `Lsl`. */
pub const SHIFT_COST: Cost = Cost {
    input_latencies: &[0, 0],
    output_latencies: &[1],
    resources: Resources::new(0x0100002),
};

/** The cost of a `Load` operation. */
pub const LOAD_COST: Cost = Cost {
    input_latencies: &[2],
    output_latencies: &[1],
    resources: Resources::new(0x0001101),
};

/** The cost of a `Load` operation. */
pub const STORE_COST: Cost = Cost {
    input_latencies: &[0, 2],
    output_latencies: &[0],
    resources: Resources::new(0x0010101),
};

/** A cost used for Debug operations. This won't affect other instructions. */
pub const DEBUG_COST: Cost = Cost {
    input_latencies: &[0],
    output_latencies: &[],
    resources: Resources::new(0x0000000),
};

//-----------------------------------------------------------------------------

/** Returns the [`Cost`] of `op`, or `None` if `op` is [`Op::Convention`]. */
pub fn op_cost(op: Op) -> Option<&'static Cost> {
    if op == Op::Convention { return None; }
    use Op::*;
    use super::code::{UnaryOp::*, BinaryOp::*};
    Some(match op {
        Convention => panic!("Cannot execute Op::Convention"),
        Constant(n) => if n == 0 { &MOVE_COST } else { &ALU_COST },
        Unary(_, op) => match op {
            Abs => &CONDITIONAL_COST,
            Negate => &ALU_COST,
            Not => &ALU_COST,
        },
        Binary(_, op) => match op {
            Add | Sub | And| Or| Xor => &ALU_COST,
            Mul => &MUL_COST,
            Lsl | Lsr | Asr => &SHIFT_COST,
            Lt | Ult | Eq | Max | Min => &CONDITIONAL_COST,
        },
        Load(_, _) => &LOAD_COST,
        Store(_, _) => &STORE_COST,
        Push => &STORE_COST,
        Pop => &LOAD_COST,
        Debug => &DEBUG_COST,
    })
}
