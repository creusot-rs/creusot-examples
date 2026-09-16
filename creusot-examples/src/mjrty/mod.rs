use creusot_std::prelude::*;

mod fortran;
mod util;

use fortran::fortran;

#[cfg(creusot)]
use util::*;

#[allow(non_snake_case)]
#[requires(A@.len() < usize::MAX@)]
#[ensures(match result {
    None => forall<x> count(A, 1, A@.len()+1, x) <= A@.len() / 2,
    Some(m) => count(A, 1, A@.len()+1, *m) > A@.len() / 2,
})]
pub fn mjrty<T: Eq + DeepModel>(A: &[T]) -> Option<&T> {
    let N = A.len();
    let mut BOOLE: bool;
    let mut CAND: Option<&T> = None;
    let mut K: usize;
    let mut I: usize;

    snapshot! { count_monotonic::<T> };

    fortran! {
                K = 0
                #[invariant(1 <= I@ && 0 <= K@ && K@ < I@ && I@ <= N@ + 1)]
                #[invariant(match CAND {
                    None => I@ == 1,
                    Some(cand) =>
                        K@ <= count(A, 1, I@, *cand) && count(A, 1, I@, *cand) <= K@ + (I@ - 1 - K@) / 2
                        && forall<x: T> x.deep_model() != cand.deep_model() ==> count(A, 1, I@, x) <= (I@ - 1 - K@) / 2,
                })]
                DO I = 1, N
                IF ((K .EQ. 0)) GOTO 'L50
                IF ((CAND .EQ. A(I))) GOTO 'L75
                K = (K - 1)
                GOTO 'L100
        'L50    CAND = A(I)
                K = 1
                GOTO 'L100
        'L75    K = (K + 1)
        'L100   CONTINUE
                IF ((K .EQ. 0)) GOTO 'L300
                BOOLE = .TRUE.
                IF ((K .GT. (N / 2))) RETURN
                K = 0
                #[invariant(1 <= I@ && I@ <= N@ + 1)]
                #[invariant(K@ <= N@ / 2)]
                #[invariant(exists<cand> CAND == Some(cand)
                    && K@ == count(A, 1, I@, *cand)
                )]
                DO I = 1, N
                IF ((CAND .NE. A(I))) GOTO 'L200
                K = (K + 1)
                IF ((K .GT. (N / 2))) RETURN
        'L200   CONTINUE
        'L300   BOOLE = .FALSE.
                RETURN
                END
    }

    // Hint for the `RETURN` of the second loop.
    proof_assert! { forall<x, i> 1 <= i && i <= N@ && x == A@[i-1]
        ==> count(A, 1, i, x) + 1 == count(A, 1, i+1, x) }

    if BOOLE { CAND } else { None }
}

#[test]
fn test() {
    assert_eq!(mjrty(&[0, 0, 0, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2]), Some(&2));
    assert_eq!(mjrty(&[0, 0, 0, 1, 1, 1, 2]), None);
}
