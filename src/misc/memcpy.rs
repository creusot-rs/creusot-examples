use creusot_contracts::*;

#[requires(tgt@.len() == src@.len())]
#[ensures((^tgt)@ == src@)]
pub fn memcpy(tgt: &mut [u8], src: & [u8]) {
    let tgt_len = snapshot! { tgt@.len() };
    let mut i = 0;
    #[invariant(tgt@.len() == *tgt_len)]
    #[invariant(i@ <= src@.len())]
    #[invariant(forall<j: Int> 0 <= j && j < i@ ==> tgt@[j] == src@[j])]
    while i < src.len() {
        tgt[i] = src[i];
        i += 1;
    }
}

#[requires(tgt@.len() == src@.len())]
#[ensures((^tgt)@ == src@)]
pub fn memcpy_itermut(tgt: &mut [u8], src: & [u8]) {
    #[invariant(forall<i : _> 0 <= i && i < produced.len() ==> ^produced[i].0 == src[i])]
    for (t, s) in tgt.iter_mut().zip(src) {
        *t = *s;
    }

    proof_assert! { tgt@.ext_eq(src@) };
}
