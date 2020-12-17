pub mod util;

pub mod x86_64;

pub mod code;

pub mod optimizer;

pub mod jit;

pub mod beetle;

pub mod buffer;
pub use buffer::{Buffer};

mod c_bindings;

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn add5() {
        use std::{mem};
        use x86_64::*;
        use Register::*;
        use BinaryOp::*;
        use Precision::*;

        let mut buffer = Buffer::new(0x1000)
            .expect("Couldn't allocate");
        let mut a = Assembler::new(&mut buffer);
        a.move_(P64, RA, RDI);
        a.const_op(Add, P64, RA, 5);
        a.ret();
        let (_, result) = buffer.execute(|bytes| {
            let f: extern "C" fn(i32) -> i32 = unsafe {mem::transmute(&bytes[0])};
            f(42)
        }).expect("Couldn't change permissions");
        assert_eq!(result, 42 + 5);
    }
}
