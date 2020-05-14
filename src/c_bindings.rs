use super::{Buffer};

/** Allocates a new empty Buffer. */
#[no_mangle]
pub extern fn mijit_new(capacity: usize) -> Option<Box<Buffer>> {
    Buffer::new(capacity).map(Box::new)
}

/** Frees a Buffer. */
#[no_mangle]
pub extern fn mijit_drop(_buffer: Box<Buffer>) {}

#[no_mangle]
pub extern fn five(/*buffer: &Buffer*/) -> i64 {
    5 //buffer.memory[0] as i64
}

#[cfg(test)]
mod tests {
    #[test]
    fn five() {
        let f = super::five();
        assert_eq!(f, 5);
    }
}
