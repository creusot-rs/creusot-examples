// Challenge 1 of VerifyThis 2026: Ada and her papers
//
// https://verifythis.github.io/onsite/archive/2026/challenge1.pdf
//
// Completed (all main tasks):
// - Safety and correctness of `compute`, `compute_opt`, `update`
//
// To do (bonus tasks):
// - Complexity
// - Variant with non-sorted input
// - Update `k` times

use creusot_std::prelude::*;

#[logic(open, inline)]
pub fn sorted_rev(s: Seq<usize>) -> bool {
    pearlite! {
    forall<i, j> 0 <= i && i <= j && j < s.len() ==> s[i]@ >= s[j]@
    }
}

#[logic]
#[requires(0 <= h && h <= s.len())]
#[ensures(0 <= result && result <= h)]
#[variant(h)]
pub fn count_higher_than(s: Seq<usize>, bound: Int, h: Int) -> Int {
    pearlite! {
        if h == 0 {
            0
        } else {
            count_higher_than(s, bound, h - 1) + if s[h - 1]@ >= bound { 1 } else { 0 }
        }
    }
}

mod lemmas {
    use super::*;

    #[logic]
    #[requires(0 <= i && i <= h && h <= s.len())]
    #[requires(forall<j> 0 <= j && j < i ==> s[j]@ >= bound)]
    #[ensures(count_higher_than(s, bound, h) >= i)]
    #[variant(h)]
    pub fn count_higher_than_ge(s: Seq<usize>, bound: Int, i: Int, h: Int) {
        if h <= 0 {
        } else if i == h {
            count_higher_than_ge(s, bound, i - 1, h - 1)
        } else {
            count_higher_than_ge(s, bound, i, h - 1)
        }
    }

    #[logic]
    #[requires(0 <= i && i <= h && h <= s.len())]
    #[requires(forall<j> i <= j && j < h ==> s[j]@ < bound)]
    #[ensures(count_higher_than(s, bound, h) <= i)]
    #[variant(h)]
    pub fn count_higher_than_le(s: Seq<usize>, bound: Int, i: Int, h: Int) {
        if h <= 0 {
        } else if i == h {
            count_higher_than_le(s, bound, i - 1, h - 1)
        } else {
            count_higher_than_le(s, bound, i, h - 1)
        }
    }

    #[check(ghost)]
    #[requires(0 <= h@ && h@ <= s@.len())]
    #[requires(forall<i> 0 <= i && i < h@ ==> s[i] >= bound)]
    #[ensures(count_higher_than(s@, bound@, s@.len()) >= h@)]
    pub fn count_higher_than_ge_ghost(s: &[usize], bound: usize, h: usize) {
        let _ = (s, bound, h);
        snapshot!(count_higher_than_ge);
    }

    #[check(ghost)]
    #[requires(0 <= l@ && l@ <= s@.len())]
    #[requires(forall<i> l@ <= i && i < s@.len() ==> s[i]@ <= bound@)]
    #[ensures(count_higher_than(s@, bound@ + 1, s@.len()) <= l@)]
    pub fn count_higher_than_le_ghost(s: &[usize], bound: usize, l: usize) {
        let _ = (s, bound, l);
        snapshot!(count_higher_than_le);
    }
}

#[logic(inline)]
pub fn has_hindex(s: Seq<usize>, idx: Int) -> bool {
    count_higher_than(s, idx, s.len()) >= idx && count_higher_than(s, idx + 1, s.len()) < idx + 1
}

#[check(terminates)]
#[requires(sorted_rev(a@))]
#[ensures(has_hindex(a@, result@))]
pub fn compute(a: &[usize]) -> usize {
    let mut h = 0usize;

    #[invariant(h@ > 0 ==> a@[h@-1]@ > h@-1)]
    #[invariant(h@ <= a@.len())]
    #[variant(a@.len() - h@)]
    while h < a.len() && h < a[h] {
        h += 1
    }

    ghost!(lemmas::count_higher_than_ge_ghost(a, h, h));
    ghost!(lemmas::count_higher_than_le_ghost(a, h, h));

    h
}

#[check(terminates)]
#[requires(sorted_rev(a@))]
#[ensures(has_hindex(a@, result@))]
pub fn compute_opt(a: &[usize]) -> usize {
    let mut lo = 0;
    let mut hi = a.len();

    #[invariant(lo <= hi && hi@ <= a@.len())]
    #[invariant(lo@ > 0 ==> a@[lo@-1]@ > lo@-1)]
    #[invariant(hi@ < a@.len() ==> a@[hi@]@ <= hi@)]
    #[variant(hi@ - lo@)]
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if a[mid] <= mid {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    ghost!(lemmas::count_higher_than_ge_ghost(a, lo, lo));
    ghost!(lemmas::count_higher_than_le_ghost(a, lo, lo));

    lo
}

#[check(terminates)]
#[requires(sorted_rev(a@))]
#[requires(has_hindex(a@, h@))]
#[requires(i@ < a@.len())]
#[requires(a@[i@] < usize::MAX)] // avoid overflow
#[ensures((^a)@.len() == (*a)@.len())]
#[ensures(sorted_rev((^a)@))] // Task 4.2
// Task 4.3: (^a) is (*a) with an element equal to (*a)[i] incremented by 1
#[ensures(exists<j> 0 <= j && j < a@.len() && (*a)@[j] == (*a)@[i@]
    && (^a)@ == (*a)@.set(j, (*a)@[j] + 1usize))]
#[ensures(has_hindex((^a)@, result@))]
pub fn update(a: &mut [usize], h: usize, i: usize) -> usize {
    let x = a[i];
    let mut lo = 0;
    let mut hi = i;
    #[invariant(lo <= hi && hi@ <= i@)]
    // the range [hi..i] is all equal to x
    #[invariant(forall<j> hi@ <= j && j < i@ ==> a@[j] == x)]
    #[invariant(lo@ == 0 || a@[lo@ - 1] > x)]
    #[variant(hi@ - lo@)]
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if a[mid] == x {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    ghost! {
        if 0 < h && a[h-1] < h {
            lemmas::count_higher_than_le_ghost(a, h-1, h-1);
            unreachable!()
        }
        if h < a.len() && a[h] > h {
            lemmas::count_higher_than_ge_ghost(a, h+1, h+1);
            unreachable!()
        }
    };

    a[lo] += 1;
    let r = if lo == h && a[lo] == h + 1 { h + 1 } else { h };
    ghost! {
        lemmas::count_higher_than_ge_ghost(a, r, r);
        lemmas::count_higher_than_le_ghost(a, r, r);
    };
    r
}

#[test]
fn test_compute() {
    let ada0 = &[12, 5, 3, 3, 3, 3, 2, 1, 0, 0];
    assert_eq!(compute_opt(ada0), 3);
    let ada1 = &[12, 5, 4, 4, 3, 3, 2, 1, 0, 0];
    assert_eq!(compute_opt(ada1), 4);
}

#[test]
fn test_update() {
    let ada = &mut [12, 5, 3, 3, 3, 3, 2, 1, 0, 0];
    assert_eq!(update(ada, 3, 5), 3);
    assert_eq!(*ada, [12, 5, 4, 3, 3, 3, 2, 1, 0, 0]);
    assert_eq!(update(ada, 3, 4), 4);
    assert_eq!(*ada, [12, 5, 4, 4, 3, 3, 2, 1, 0, 0]);
}
