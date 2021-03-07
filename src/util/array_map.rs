use std::fmt::{Debug};
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
 * This is preferable to a HashMap when possible.
 */
#[derive(Debug, Clone)]
pub struct ArrayMap<K: AsUsize, V>(
    Box<[V]>,
    PhantomData<K>,
);

impl<K: AsUsize, V> ArrayMap<K, V> {
    pub fn new(length: usize) -> Self where V: Default {
        Self::new_with(length, || Default::default())
    }

    pub fn new_with(length: usize, f: impl Fn() -> V) -> Self {
        ArrayMap(
            (0..length).map(|_| f()).collect(),
            PhantomData,
        )
    }

    pub fn len(&self) -> usize { self.0.len() }

    pub fn iter(&self) -> std::slice::Iter<V> { self.0.iter() }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<V> { self.0.iter_mut() }
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
