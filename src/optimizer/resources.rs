use std::cmp::{PartialOrd, Ordering};
use std::num::{Wrapping};
use std::ops::{Add, Sub};

/** Has ones above the top bit of each base-8 digit. */
const CARRY_MASK: Wrapping<u64> = Wrapping(0x9249249249249248);

/**
 * Represents a collection of finite resources.
 * A Resources can record up to 7 units of each of 21 distinct resources,
 * using the base-8 digits of a 64-bit integer.
 */
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Resources(std::num::Wrapping<u64>);

impl Resources {
    pub fn new(amounts: &[u8]) -> Self {
        assert!(amounts.len() <= 21);
        let mut ret = Wrapping(0);
        for (i, &amount) in amounts.iter().enumerate() {
            assert!(amount < 8);
            ret |= Wrapping(amount as u64) << (3*i);
        }
        Resources(ret)
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

impl Sub for Resources {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        let ret = self.0 - rhs.0;
        assert_eq!((self.0 ^ rhs.0 ^ ret) & CARRY_MASK, Wrapping(0));
        Resources(ret)
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn fixtures() -> [Resources; 4] {
        [
            Resources::new(&[3, 3]),
            Resources::new(&[3, 5]),
            Resources::new(&[5, 3]),
            Resources::new(&[5, 5]),
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
        let _ = Resources::new(&[3]) + Resources::new(&[5]);
    }

    #[test]
    #[should_panic]
    fn underflow() {
        let _ = Resources::new(&[3]) - Resources::new(&[5]);
    }
}
