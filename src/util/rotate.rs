/** Bitwise left rotate. */
pub fn rotate_left(x: u64, shift: u32) -> u64 {
    let shift = shift & 0x3F;
    if shift == 0 {
        // Avoid shifting by 64 places.
        return x;
    }
    (x << shift) | (x >> (64 - shift))
}

/** Bitwise right rotate. */
pub fn rotate_right(x: u64, shift: u32) -> u64 {
    let shift = shift & 0x3F;
    if shift == 0 {
        // Avoid shifting by 64 places.
        return x;
    }
    (x << (64 - shift)) | (x >> shift)
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn rotate() {
        let x = 0x0123456789ABCDEF;
        assert_eq!(rotate_left(x, 0), x);
        assert_eq!(rotate_right(x, 0), x);
        assert_eq!(rotate_left(x, 16), 0x456789ABCDEF0123);
        assert_eq!(rotate_right(x, 16), 0xCDEF0123456789AB);
        assert_eq!(rotate_left(x, 64), x);
        assert_eq!(rotate_right(x, 64), x);
        assert_eq!(rotate_left(x, 80), 0x456789ABCDEF0123);
        assert_eq!(rotate_right(x, 80), 0xCDEF0123456789AB);
    }
}
