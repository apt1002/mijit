use std::fmt::{self, Debug, Formatter};
use std::cmp::{PartialOrd, Ordering};
use std::num::{Wrapping};
use std::ops::{Add, AddAssign, Sub, SubAssign};

/// Has ones above the top bit of each hexadecimal digit.
const CARRY_MASK: Wrapping<u64> = Wrapping(0x1111111111111110);

/// Represents a collection of finite resources.
/// A `Resources` can record up to 15 units of each of 15 distinct resources,
/// using the hexadecimal digits of a 64-bit integer.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Resources(std::num::Wrapping<u64>);

impl Resources {
    pub const fn new(hex: u64) -> Self {
        // assert!(hex < 1<<60); // Not allowed in a const fn.
        Resources(Wrapping(hex))
    }
}

impl Debug for Resources {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{:#x}", self.0)
    }
}

impl PartialOrd for Resources {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Ordering::*;
        match (other.ge(self), self.ge(other)) {
            (false, false) => None,
            (false, true) => Some(Greater),
            (true, false) => Some(Less),
            (true, true) => Some(Equal),
        }
    }

    fn lt(&self, other: &Self) -> bool { other != self && other.ge(self) }
    fn gt(&self, other: &Self) -> bool { self != other && self.ge(other) }
    fn le(&self, other: &Self) -> bool { other.ge(self) }

    fn ge(&self, other: &Self) -> bool {
        let borrows = (self.0 ^ other.0) ^ (self.0 - other.0);
        (borrows & CARRY_MASK) == Wrapping(0)
    }
}

impl Add for Resources {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let ret = self.0 + rhs.0;
        assert_eq!((self.0 ^ rhs.0 ^ ret) & CARRY_MASK, Wrapping(0));
        Resources(ret)
    }
}

impl AddAssign for Resources {
    fn add_assign(&mut self, other: Self) {
        *self = self.add(other);
    }
}

impl Sub for Resources {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        let ret = self.0 - rhs.0;
        assert_eq!((self.0 ^ rhs.0 ^ ret) & CARRY_MASK, Wrapping(0));
        Resources(ret)
    }
}

impl SubAssign for Resources {
    fn sub_assign(&mut self, other: Self) {
        *self = self.sub(other);
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn fixtures() -> [Resources; 4] {
        [
            Resources::new(0x33),
            Resources::new(0x53),
            Resources::new(0x35),
            Resources::new(0x55),
        ]
    }

    #[test]
    fn ord() {
        use Ordering::*;
        for (i, &x) in fixtures().iter().enumerate() {
            for (j, &y) in fixtures().iter().enumerate() {
                assert_eq!(x <= y, (i & !j) == 0);
                assert_eq!(x >= y, (!i & j) == 0);
                match x.partial_cmp(&y) {
                    None => {
                        assert!(!x.lt(&y));
                        assert!(!x.le(&y));
                        assert!(!x.gt(&y));
                        assert!(!x.ge(&y));
                        assert!(!x.eq(&y));
                    },
                    Some(Less) => {
                        assert!(x.lt(&y));
                        assert!(x.le(&y));
                        assert!(!x.gt(&y));
                        assert!(!x.ge(&y));
                        assert!(!x.eq(&y));
                    },
                    Some(Equal) => {
                        assert!(!x.lt(&y));
                        assert!(x.le(&y));
                        assert!(!x.gt(&y));
                        assert!(x.ge(&y));
                        assert!(x.eq(&y));
                    },
                    Some(Greater) => {
                        assert!(!x.lt(&y));
                        assert!(!x.le(&y));
                        assert!(x.gt(&y));
                        assert!(x.ge(&y));
                        assert!(!x.eq(&y));
                    },
                }
            }
        }
    }

    #[test]
    fn add_sub() {
        for &x in &fixtures() {
            for &y in &fixtures() {
                if x <= y {
                    let z = y - x;
                    assert_eq!(z+x, y);
                }
            }
        }
    }

    #[test]
    #[should_panic]
    fn overflow() {
        let _ = Resources::new(0x3) + Resources::new(0xd);
    }

    #[test]
    #[should_panic]
    fn underflow() {
        let _ = Resources::new(0x3) - Resources::new(0xd);
    }
}
