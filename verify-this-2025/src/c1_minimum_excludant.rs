//! Challenge 1 of VerifyThis 2025
//!
//! https://verifythis.github.io/onsite/archive/2025/

use creusot_std::logic::Mapping;
use creusot_std::prelude::{vec, *};

// Version 0: Naive implementation

// Minimal version of `mex0` for which we can prove safety (here: no out of bounds accesses).
// The trivial `invariant(true)` enables a Creusot-specific desugaring of the for loop
// which is sufficient to expose the fact that `i` is in the range `0..n`.
// The trivial `ensures(true)` is to enable compiling with rustc (attributes on expressions
// like `invariant(true)` are unstable, so `ensures` removes them in normal compilation.)
#[ensures(true)]
pub fn mex0_safety(a: &[usize]) -> usize {
    let n = a.len();
    'outer: for v in 0..n {
        #[invariant(true)]
        for i in 0..n {
            if a[i] == v {
                continue 'outer;
            }
        }
        return v;
    }
    n
}

#[ensures(!a@.contains(result))]
#[ensures(forall<x> x < result ==> a@.contains(x))]
pub fn mex0(a: &[usize]) -> usize {
    let n = a.len();
    let mut _idx = snapshot! { |i: Int| i };
    #[invariant(forall<x> 0 <= x && x < produced.len() ==> 0 <= _idx[x] && _idx[x] < n@ && a@[_idx[x]]@ == x)]
    'outer: for v in 0..n {
        #[invariant(!a@[..produced.len()].contains(v))]
        for i in 0..n {
            if a[i] == v {
                ghost! { _idx = snapshot! { _idx.set(v@, i@) } };
                continue 'outer;
            }
        }
        proof_assert! { a@ == a@[..n@] };
        proof_assert! { forall<x> x < v ==> a@[_idx[x@]] == x };
        return v;
    }
    ghost! { apply_mex_lemma(_idx, a) };
    n
}

#[check(ghost)]
#[requires(forall<x> 0 <= x && x < a@.len() ==> 0 <= idx[x] && idx[x] < a@.len() && a@[idx[x]]@ == x)]
#[ensures(forall<n: T> n@ == a@.len() ==> !a@.contains(n))]
fn apply_mex_lemma<T: View<ViewTy = Int>>(idx: Snapshot<Mapping<Int, Int>>, a: &[T]) {
    let _ = (idx, a);
    let _ = snapshot! { mex_lemma::<T> };
}

#[logic]
#[requires(forall<x> 0 <= x && x < a.len() ==> 0 <= idx[x] && idx[x] < a.len() && a[idx[x]]@ == x)]
#[requires(0 <= i && i < a.len() && a[i]@ == a.len())]
#[ensures(false)]
fn mex_lemma<T: View<ViewTy = Int>>(idx: Mapping<Int, Int>, a: Seq<T>, i: Int) {
    pigeonhole(a.len() + 1, a.len(), idx.set(a.len(), i))
}

// Pigeonhole principle as a logic function.
#[logic]
#[requires(0 <= m && m < n)]
#[requires(forall<i> 0 <= i && i < n ==> 0 <= f[i] && f[i] < m)]
#[ensures(exists<i1, i2> 0 <= i1 && i1 < i2 && i2 < n && f[i1] == f[i2])]
fn pigeonhole(n: Int, m: Int, f: Mapping<Int, Int>) {
    let _ = use_pigeonhole_builtin;
}

// Depend on this to import the pigeonhole principle from Why3
// Not actually callable!
#[logic]
#[builtin("pigeon.Pigeonhole.pigeonhole")]
fn use_pigeonhole_builtin() {}

// Version 1: Boolean marks

// Prove only safety
#[ensures(true)]
pub fn mex1_safety(a: &[usize]) -> usize {
    let n = a.len();
    let mut seen = vec![false; n];
    #[invariant(seen@.len() == n@)]
    for &x in a {
        if x < n {
            seen[x] = true;
        }
    }
    #[invariant(true)]
    for i in 0..n {
        if !seen[i] {
            return i;
        }
    }
    return n;
}

#[ensures(!a@.contains(result))]
#[ensures(forall<x> x < result ==> a@.contains(x))]
pub fn mex1(a: &[usize]) -> usize {
    let n = a.len();
    let mut seen = vec![false; n];
    let mut _idx = snapshot! { |i: Int| i };
    #[invariant(seen@.len() == n@)]
    #[invariant(forall<x> 0 <= x && x < n@ && seen@[x] ==> 0 <= _idx[x] && _idx[x] < n@ && a@[_idx[x]]@ == x)]
    #[invariant(forall<j> 0 <= j && j < produced.len() && a@[j] < n ==> seen@[a@[j]@] && 0 <= _idx[a@[j]@] && _idx[a@[j]@] < n@ && a@[_idx[a@[j]@]] == a@[j])]
    for &x in a {
        if x < n {
            seen[x] = true;
        }
        ghost! { _idx = snapshot! { _idx.set(x@, produced.len() - 1) } };
    }
    #[invariant(forall<x> 0 <= x && x < produced.len() ==> 0 <= _idx[x] && _idx[x] < n@ && a@[_idx[x]]@ == x)]
    for i in 0..n {
        if !seen[i] {
            proof_assert! { forall<x> x < i ==> a@[_idx[x@]] == x };
            return i;
        }
    }
    ghost! { apply_mex_lemma(_idx, a) };
    return n;
}

// Version 2: Mutated array

#[ensures((^a)@.permutation_of((*a)@))]
#[ensures(!a@.contains(result))]
#[ensures(forall<x> x < result ==> a@.contains(x))]
pub fn mex2(a: &mut [usize]) -> usize {
    let _a = snapshot! { a@ };
    let n = a.len();
    let mut i = 0;
    #[invariant(a@.permutation_of(*_a))]
    #[invariant(forall<j> 0 <= j && j < i@ && a@[j]@ < n@ ==> a@[a@[j]@] == a@[j])]
    while i < n {
        let x = a[i];
        if x >= n || a[x] == x {
            i += 1;
        } else {
            a.swap(i, x);
            if x < i {
                i += 1;
            }
        }
    }
    #[invariant(forall<j> 0 <= j && j < produced.len() ==> a@[j]@ == j)]
    for i in 0..n {
        if i != a[i] {
            proof_assert! { forall<j: usize> j < i ==> a@[j@] == j };
            return i;
        }
    }
    proof_assert! { forall<j: usize> j < n ==> a@[j@] == j };
    n
}

// Version 3: Sorted array

#[logic(open)]
pub fn sorted<T: DeepModel>(a: Seq<T>) -> bool
where
    T::DeepModelTy: OrdLogic,
{
    pearlite! { forall<i, j> 0 <= i && i < j && j < a.len() ==> a[i].deep_model() <= a[j].deep_model() }
}

#[requires(a@.len() < isize::MAX@)]
#[requires(sorted(a@))]
#[ensures(!a@.contains(result))]
#[ensures(forall<x> 0isize <= x && x < result ==> a@.contains(x))]
pub fn mex3(a: &[isize]) -> isize {
    let n = a.len();
    let mut last = -1;
    let mut _idx = snapshot! { |i: Int| i };
    #[invariant(-1 <= last@ && last@ < n@)]
    #[invariant(forall<x> 0 <= x && x <= last@ ==> 0 <= _idx[x] && _idx[x] < n@ && a@[_idx[x]]@ == x)]
    #[invariant(forall<j> 0 <= j && j < produced.len() && 0 <= a@[j]@ ==> a@[j] <= last)]
    for i in 0..n {
        if a[i] >= last + 2 {
            proof_assert! { forall<x: isize> 0 <= x@ && x <= last ==> a@[_idx[x@]] == x };
            return last + 1;
        } else if a[i] >= 0 {
            last = a[i];
            ghost! { _idx = snapshot! { _idx.set(a@[i@]@, i@) } };
        }
        ghost! {
            if last >= 0 && last as usize >= n { apply_mex_lemma(_idx, a) }
        };
    }
    proof_assert! { forall<x: isize> 0 <= x@ && x <= last ==> a@[_idx[x@]] == x };
    last + 1
}
