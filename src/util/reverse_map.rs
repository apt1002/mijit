use std::collections::{HashMap};
use std::hash::{Hash};

/// Given a `HashMap<K, V>`, return a `HashMap<V, K>`.
/// If more than one `K` maps to the same `V`, pick one arbitrarily.
#[allow(unused)]
pub fn reverse_map<K, V>(k_to_v: &HashMap<K, V>) -> HashMap<V, K> where
    K: Clone + Hash + Eq,
    V: Clone + Hash + Eq,
{
    k_to_v.iter().map(|(k, v)| (v.clone(), k.clone())).collect()
}