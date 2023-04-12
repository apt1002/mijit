use std::iter::{FusedIterator};

/// Return the index in `it` of the element for which `f` gives the largest
/// non-None result.
pub fn map_filter_max<I: IntoIterator, T: Ord> (
    it: I,
    mut f: impl FnMut(I::Item) -> Option<T>,
) -> Option<usize> {
    let mut it = it.into_iter().enumerate();
    while let Some((i, x)) = it.next() {
        if let Some(fx) = f(x) {
            let mut best = (i, fx);
            for (j, y) in it {
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

//-----------------------------------------------------------------------------

/// A function that is ad-hoc polymorphic on its input type.
///
/// A function that accepts `(&T, &U)` will also accept `&(T, U)`.
/// A function that accepts `(&mut T, &mut U)` will also accept `&mut (T, U)`.
pub trait AdHocFn<Input> {
    type Output;
    fn call(&self, input: Input) -> Self::Output;
}

impl<'a, T, U, F: AdHocFn<(&'a T, &'a U)>> AdHocFn<&'a (T, U)> for F {
    type Output = F::Output;

    fn call(&self, input: &'a (T, U)) -> Self::Output {
        self.call((&input.0, &input.1))
    }
}

impl<'a, T, U, F: AdHocFn<(&'a mut T, &'a mut U)>> AdHocFn<&'a mut (T, U)> for F {
    type Output = F::Output;

    fn call(&self, input: &'a mut (T, U)) -> Self::Output {
        self.call((&mut input.0, &mut input.1))
    }
}

/// Maps `(T, U)` to `T`.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct First;

impl<T, U> AdHocFn<(T, U)> for First {
    type Output = T;
    fn call(&self, input: (T, U)) -> T { input.0 }
}

/// Maps `(T, U)` to `U`.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Second;

impl<T, U> AdHocFn<(T, U)> for Second {
    type Output = U;
    fn call(&self, input: (T, U)) -> U { input.1 }
}

//-----------------------------------------------------------------------------

/// Similar to [`std::iter::Map`] but easier to name.
pub struct Map<I: Iterator, F: AdHocFn<I::Item>>(pub I, pub F);

impl<I: Iterator, F: AdHocFn<I::Item>> Iterator for Map<I, F> {
    type Item = F::Output;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|x| self.1.call(x))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<I: DoubleEndedIterator, F: AdHocFn<I::Item>> DoubleEndedIterator for Map<I, F> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|x| self.1.call(x))
    }
}

impl<I: ExactSizeIterator, F: AdHocFn<I::Item>> ExactSizeIterator for Map<I, F> {}

impl<I: FusedIterator, F: AdHocFn<I::Item>> FusedIterator for Map<I, F> {}
