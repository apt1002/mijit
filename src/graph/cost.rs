use super::{Op, Resources};

/// The CPU resources available per cycle. The different resources are as
/// follows (modelled on Skylake):
///  - The number of instructions decoded.
///  - The number of flag-using macro instructions (this is a hack).
///  - The number of address generation units.
///  - The number of load units.
///  - The number of store units.
///  - The number of arithmetic / logic units.
///  - The number of multiplication units.
/// These correspond to the hexadecimal digits of the [`Resources`] from least
/// to most significant.
pub const BUDGET: Resources = Resources::new(0x1412316);

/// The resources needed to spill a value.
pub const SPILL_COST: Resources = Resources::new(0x0010202);

/// The additional resources needed per operand that is a [`Slot`].
///
/// [`Slot`]: super::code::Slot
pub const SLOT_COST: Resources = Resources::new(0x0001100);

//-----------------------------------------------------------------------------

/// Represents the cost of executing an [`Op`] (for example).
#[derive(Debug)]
pub struct Cost {
    /// The number of cycles after executing the `Op` that its result appears.
    /// If there's no result, use `0xFF`.
    pub latency: u8,
    /// The execution resources are occupied by the `Op`.
    pub resources: Resources,
}

/// The cost of a no-op.
pub const INPUT_COST: Cost = Cost {
    latency: 0,
    resources: Resources::new(0x0000000),
};

/// The cost of a compare and branch.
pub const GUARD_COST: Cost = Cost {
    latency: 0xFF,
    resources: Resources::new(0x0100012),
};

/// The cost of a typical `Constant`.
pub const CONST_COST: Cost = Cost {
    latency: 0,
    resources: Resources::new(0x0100001),
};

/// The cost of a typical unary ALU operation such as `Not`, `Neg`.
pub const UNARY_COST: Cost = Cost {
    latency: 1,
    resources: Resources::new(0x0100001),
};

/// The cost of a typical binary ALU operation such as `Add`, `And`.
pub const BINARY_COST: Cost = Cost {
    latency: 1,
    resources: Resources::new(0x0100001),
};

/// The cost of a unary conditional operation such as `Abs`.
pub const ABS_COST: Cost = Cost {
    latency: 2,
    resources: Resources::new(0x0200013),
};

/// The cost of a binary conditional operation such as `Abs`, `Max`.
pub const CONDITIONAL_COST: Cost = Cost {
    latency: 2,
    resources: Resources::new(0x0200013),
};

/// The cost of a `Mul` operation.
pub const MUL_COST: Cost = Cost {
    latency: 3,
    resources: Resources::new(0x1100001),
};

/// The cost of a `UDiv` or `SDiv` operation.
pub const DIV_COST: Cost = Cost {
    latency: 30,
    resources: Resources::new(0x1012306),
};

/// The cost of a typical shift operation such as `Lsl`.
pub const SHIFT_COST: Cost = Cost {
    latency: 1,
    resources: Resources::new(0x0100002),
};

/// The cost of a `Load` operation.
pub const LOAD_COST: Cost = Cost {
    latency: 3,
    resources: Resources::new(0x0001101),
};

/// The cost of a `Load` operation.
pub const STORE_COST: Cost = Cost {
    latency: 0,
    resources: Resources::new(0x0010101),
};

/// The cost of a `Send` operation.
pub const SEND_COST: Cost = Cost {
    latency: 0,
    resources: Resources::new(0x0000000),
};

/// A cost used for Debug operations. This won't affect other instructions.
pub const DEBUG_COST: Cost = Cost {
    latency: 0xFF,
    resources: Resources::new(0x0000000),
};

//-----------------------------------------------------------------------------

/// Returns the [`Cost`] of `op`.
#[allow(clippy::module_name_repetitions)]
pub fn op_cost(op: Op) -> &'static Cost {
    use Op::*;
    use super::code::{UnaryOp::*, BinaryOp::*};
    match op {
        Guard => &GUARD_COST,
        Input => &INPUT_COST,
        Constant(_) => &CONST_COST, // TODO: Make the cost depend on `n`.
        Unary(_, op) => match op {
            Abs => &ABS_COST,
            Negate | Not => &UNARY_COST,
        },
        Binary(_, op) => match op {
            Add | Sub | And| Or| Xor => &BINARY_COST,
            Mul => &MUL_COST,
            UDiv | SDiv => &DIV_COST,
            Lsl | Lsr | Asr => &SHIFT_COST,
            Lt | Ult | Eq | Max | Min => &CONDITIONAL_COST,
        },
        Load(_, _) => &LOAD_COST,
        Store(_, _) => &STORE_COST,
        Send => &SEND_COST,
        Debug => &DEBUG_COST,
    }
}
