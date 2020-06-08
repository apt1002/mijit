use super::{code, control_flow};

pub struct CallingConvention;

pub struct History<A: control_flow::Address> {
    pub test: code::TestOp,
    pub fetch: Vec<code::Action<A>>,
    pub calling_convention: CallingConvention,
    pub register: code::R,
    pub retire: Vec<code::Action<A>>,
}
