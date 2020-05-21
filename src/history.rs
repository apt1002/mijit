use super::{code, control_flow};

pub struct CallingConvention;

pub struct History<A: control_flow::Address> {
    pub fetch: code::Code<A>,
    pub retire: code::Code<A>,
    pub calling_convention: CallingConvention,
}
