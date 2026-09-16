use creusot_std::prelude::*;

/// Number of `x` in `v` between indices `i` and `j` (excluded), where those
/// indices are 1-indexed.
/// We actually compare the `.deep_model()` of the elements.
#[logic(open)]
#[requires(1 <= i && i <= j && j <= v@.len() + 1)]
#[ensures(0 <= result && result <= j - i)]
#[variant(j)]
pub fn count<T: DeepModel>(v: &[T], i: Int, j: Int, x: T) -> Int {
    pearlite! {
        count_(v, i, j, x.deep_model())
    }
}

/// Only recurse after applying `deep_model` so that `count` is automatically
/// invariant up to `deep_model`:
/// `x.deep_model() == y.deep_model() ==> count(v, i, j, x) == count(v, i, j, y)`.
#[logic(open)]
#[requires(1 <= i && i <= j && j <= v@.len() + 1)]
#[ensures(0 <= result && result <= j - i)]
#[variant(j)]
pub fn count_<T: DeepModel>(v: &[T], i: Int, j: Int, x: T::DeepModelTy) -> Int {
    pearlite! {
        if j <= i {
            0
        } else if v@[j-2].deep_model() == x {
            1 + count_(v, i, j - 1, x)
        } else {
            count_(v, i, j - 1, x)
        }
    }
}

#[logic]
#[requires(1 <= i && i <= j && j <= j2 && j2 <= v@.len() + 1)]
#[ensures(count(v, i, j, x) <= count(v, i, j2, x))]
#[variant(j2)]
pub fn count_monotonic<T: DeepModel>(v: &[T], i: Int, j: Int, j2: Int, x: T) {
    pearlite! {
        if j < j2 {
            count_monotonic(v, i, j, j2-1, x)
        }
    }
}
