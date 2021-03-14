/**
 * Return the index in `it` of the element for which `f` gives the largest
 * non-None result.
 */
pub fn map_filter_max<I: IntoIterator, T: Ord> (
    it: I,
    mut f: impl FnMut(I::Item) -> Option<T>,
) -> Option<usize> {
    let mut it = it.into_iter().enumerate();
    while let Some((i, x)) = it.next() {
        if let Some(fx) = f(x) {
            let mut best = (i, fx);
            while let Some((j, y)) = it.next() {
                if let Some(fy) = f(y) {
                    if fy > best.1 {
                        best = (j, fy);
                    }
                }
            }
            return Some(best.0);
        }
    }
    None
}
