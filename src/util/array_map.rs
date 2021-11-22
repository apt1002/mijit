use std::fmt::{self, Debug, Formatter};
use std::hash::{Hash};
use std::marker::{PhantomData};

/**
 * Internally represented as a small integer that is usable as an array index.
 */
pub trait AsUsize: Debug + Copy + Hash + Eq {
    fn as_usize(self) -> usize;
}

/**
 * A map that is implemented as an array.
 * This is preferable to a `HashMap` when possible.
 */
#[derive(Clone)]
pub struct ArrayMap<K: AsUsize, V>(
    Box<[V]>,
    PhantomData<K>,
);

impl<K: AsUsize, V> ArrayMap<K, V> {
    pub fn new_with(length: usize, f: impl Fn() -> V) -> Self {
        (0..length).map(|_| f()).collect()
    }

    pub fn new(length: usize) -> Self where V: Default {
        Self::new_with(length, Default::default)
    }

    pub fn is_empty(&self) -> bool { self.0.len() == 0 }

    pub fn len(&self) -> usize { self.0.len() }

    pub fn iter(&self) -> std::slice::Iter<V> { self.0.iter() }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<V> { self.0.iter_mut() }
}

impl<K: AsUsize, V: Debug> Debug for ArrayMap<K, V> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        self.0.fmt(f)
    }
}

impl<'a, K: AsUsize, V> IntoIterator for &'a ArrayMap<K, V> {
    type Item = &'a V;
    type IntoIter = std::slice::Iter<'a, V>;

    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

impl<'a, K: AsUsize, V> IntoIterator for &'a mut ArrayMap<K, V> {
    type Item = &'a mut V;
    type IntoIter = std::slice::IterMut<'a, V>;

    fn into_iter(self) -> Self::IntoIter { self.iter_mut() }
}

impl<K: AsUsize, V> FromIterator<V> for ArrayMap<K, V> {
    fn from_iter<T: IntoIterator<Item=V>>(iter: T) -> Self {
        ArrayMap(iter.into_iter().collect(), PhantomData)
    }
}

impl<K: AsUsize, V> AsRef<[V]> for ArrayMap<K, V> {
    fn as_ref(&self) -> &[V] { self.0.as_ref() }
}

impl<K: AsUsize, V> AsMut<[V]> for ArrayMap<K, V> {
    fn as_mut(&mut self) -> &mut [V] { self.0.as_mut() }
}

impl<K: AsUsize, V> std::ops::Index<K> for ArrayMap<K, V> {
    type Output = V;

    fn index(&self, index: K) -> &V {
        &self.0[index.as_usize()]
    }
}

impl<K: AsUsize, V> std::ops::IndexMut<K> for ArrayMap<K, V> {
    fn index_mut(&mut self, index: K) -> &mut V {
        &mut self.0[index.as_usize()]
    }
}

//-----------------------------------------------------------------------------

/**
 * Declares a new type that wraps an array index but such that `Option<Self>`
 * is the same size as `Self`. This is similar to `std::num::NonZeroXXX` except
 * that the excluded value is the maximum value, not zero.
 *
 * Usage:
 * ```
 * array_index! {
 *     /// Documentation.
 *     #[attributes]
 *     pub struct MyStruct(NonZeroU16) {
 *         debug_name: "MyStruct",
 *         UInt: u16,
 *     }
 * }
 * ```
 */
macro_rules! array_index {
    (
        $(#[$struct_attributes: meta])*
        pub struct $Name: ident(
            $(#[$field_attributes: meta])*
            $NonZeroUInt: ty
        ) {
            debug_name: $debug_name: expr,
            UInt: $UInt: ty,
        }
    ) => {
        $(#[$struct_attributes])*
        #[repr(transparent)]
        pub struct $Name(
            $(#[$field_attributes])*
            $NonZeroUInt
        );

        impl $Name {
            /**
             * Safety
             *
             * We reserve the maximum value rather than zero.
             * The maximum value is not usable as an array index anyway,
             * because it is not less than the maximum length.
             */
            #[allow(clippy::missing_safety_doc)] // Work around bug in clippy.
            #[allow(dead_code)]
            pub const unsafe fn new_unchecked(index: $UInt) -> Self {
                Self(<$NonZeroUInt>::new_unchecked(index + 1))
            }

            #[allow(dead_code)]
            pub const fn new(index: $UInt) -> Option<Self> {
                #[allow(clippy::manual_map)] // Work around bug in clippy.
                match <$NonZeroUInt>::new(index.wrapping_add(1)) {
                    Some(index) => Some(Self(index)),
                    None => None,
                }
            }
        }

        impl std::fmt::Debug for $Name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
                use crate::util::AsUsize;
                write!(f, "{}({:?})", $debug_name, self.as_usize())
            }
        }

        impl crate::util::AsUsize for $Name {
            fn as_usize(self) -> usize {
                self.0.get() as usize - 1
            }
        }
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    use std::num::NonZeroU8;

    #[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
    #[repr(transparent)]
    struct Foo(NonZeroU8);

    impl Foo {
        fn new(index: u8) -> Self {
            let index = NonZeroU8::new(index + 1).expect("Not a valid array index");
            Self(index)
        }
    }

    impl std::fmt::Debug for Foo {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
            write!(f, "Foo({:?})", self.as_usize())
        }
    }

    impl AsUsize for Foo {
        fn as_usize(self) -> usize {
            self.0.get() as usize - 1
        }
    }

    #[test]
    fn array_map() {
        assert_eq!(std::mem::size_of::<Foo>(), 1);
        assert_eq!(std::mem::size_of::<Option<Foo>>(), 1);
        let i = Foo::new(1);
        assert_eq!(i.0.get(), 2);
        assert_eq!(i.as_usize(), 1);
        assert_eq!(format!("{:#?}", i), "Foo(1)");
        let mut a = ArrayMap::new(2);
        assert_eq!(a.as_ref(), &[false, false]);
        assert_eq!(a.as_mut(), &[false, false]);
        a[i] = true;
        assert_eq!(a.as_ref(), &[false, true]);
        for (i, r) in a.iter().enumerate() {
            assert_eq!(*r, i>0);
        }
        for r in &mut a {
            *r = !*r;
        }
        assert_eq!(a.as_ref(), &[true, false]);
        a.as_mut()[1] = true;
        assert_eq!(a.as_ref(), &[true, true]);
    }
}
