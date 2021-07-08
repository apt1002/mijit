/** Generate a pseudo-random permutation of size `size`. */
pub fn permutation(size: usize) -> Vec<usize> {
    let mut nats: Vec<usize> = (0..size).collect();
    let mut seed: u32 = 1;
    (0..size).map(|_| {
        seed = seed.wrapping_mul(314159265).wrapping_add(271828183);
        let index = (nats.len() as u64) * (seed as u64) >> 32;
        nats.swap_remove(index as usize)
    }).collect()
}
