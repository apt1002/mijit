pub mod code;

pub mod x86_64;
pub use x86_64::{Assembler};

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

        let mut buffer = Buffer::new(0x1000)
            .expect("Couldn't allocate");
        let mut a = Assembler::new(&mut buffer);
        a.mov(RA, RDI);
        a.const_op(Add, RA, 5);
        a.ret();
        let (_, result) = buffer.execute(|bytes| {
            let f: extern "C" fn(i32) -> i32 = unsafe {mem::transmute(&bytes[0])};
            f(42)
        }).expect("Couldn't change permissions");
        assert_eq!(result, 42 + 5);
    }
}
