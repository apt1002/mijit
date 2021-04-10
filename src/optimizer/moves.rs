use std::collections::{HashMap};
use std::fmt::{Debug};
use std::hash::{Hash};

/**
 * Find a sequence of moves to implement the specified mapping `dest_to_src`.
 * Returns a sequence of (dest, src) pairs.
 *
 *  - dest_to_src - for each destination V, the corresponding source V.
 *  - temp - a temporary location used to break cycles.
 */
pub fn moves<V: Debug + Clone + Hash + Eq>(
    mut dest_to_src: HashMap<V, V>,
    temp: &V,
) -> impl Iterator<Item=(V, V)> {
    // Make a work list that won't change as we remove elements from the map.
    let dests: Vec<V> = dest_to_src.iter().map(|(dest, src)| {
        assert_ne!(src, temp);
        dest.clone()
    }).collect();
    // Loop through the work list.
    let mut moves: Vec<(V, V)> = Vec::new(); // In reverse order.
    let mut chain: Vec<V> = Vec::new(); // In forwards order.
    for mut current in dests {
        // Follow the chain starting at `current`.
        while let Some(src) = dest_to_src.remove(&current) {
            if src == current {
                // Optimized case: remove a trivial cycle.
                break;
            }
            chain.push(current);
            current = src;
        }
        // If the chain ended with a non-trivial cycle, break it.
        let cycle = chain.iter().find(|&dest: &&V| dest == &current).cloned();
        if cycle.is_some() {
            current = temp.clone();
        }
        // Process the chain.
        while let Some(dest) = chain.pop() {
            moves.push((dest.clone(), current));
            current = dest;
        }
        // Close the cycle, if any.
        if let Some(src) = cycle {
            moves.push((temp.clone(), src));
        }
        assert_eq!(chain.len(), 0);
    }
    moves.into_iter().rev()
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_small() {
        const N: usize = 5;
        const N1: usize = N + 1;
        // Construct the input.
        let mut input = [0; N1];
        for src in 0..N1 {
            input[src] = src + 10;
        }
        for test in 0..(N1.pow(N as u32)) {
            // Construct the test case.
            let mut dest_to_src = HashMap::new();
            let mut i = test;
            for dest in 0..N {
                let src = i % N1;
                i /= N1;
                if src < N {
                    dest_to_src.insert(dest, src);
                }
            }
            // Construct the expected output.
            let mut expected = input;
            for (&dest, &src) in &dest_to_src {
                expected[dest] = input[src]
            }
            // Construct the observed output.
            let pairs: Vec<_> = moves(dest_to_src, &N).collect();
            let mut observed = input;
            for &(dest, src) in &pairs {
                observed[dest] = observed[src];
            }
            // Report a failure if they don't match.
            if expected[..N] != observed[..N] {
                println!("Test: {:#?}", test);
                println!("Input: {:#?}", &input[..N]);
                println!("Expected: {:#?}", &expected[..N]);
                println!("Attempt:");
                for (dest, src) in pairs {
                    println!("  Move {:#?} <- {:#?}", dest, src);
                }
                println!("Observed: {:#?}", &observed[..N]);
                panic!("Attempt does not work");
            }
        }
    }
}
