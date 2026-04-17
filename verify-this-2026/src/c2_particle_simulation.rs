use creusot_std::{
    ghost::{
        invariant::{AtomicInvariantSC, Protocol, declare_namespace},
        perm::Perm,
    },
    prelude::{vec, *},
    std::thread::{self, JoinHandleExt},
};
use std::thread::ScopedJoinHandle;

mod bag {
    use creusot_std::{
        ghost::{
            Container, FnGhost,
            perm::{Perm, SendPerm, SyncPerm},
        },
        logic::FSet,
        prelude::*,
    };

    #[opaque]
    pub struct Bag;

    impl Container for Bag {
        type Value = FSet<i32>;
    }

    impl SendPerm for Bag {}
    impl SyncPerm for Bag {}

    #[opaque]
    pub struct Committer;

    impl Committer {
        #[logic(opaque)]
        pub fn ward(self) -> Bag {
            dead
        }

        #[logic(opaque)]
        pub fn shot(self) -> bool {
            dead
        }

        #[logic(opaque)]
        pub fn val_before(self) -> FSet<i32> {
            dead
        }

        #[logic(opaque)]
        pub fn val_after(self) -> FSet<i32> {
            dead
        }

        #[logic(open, inline)]
        pub fn hist_inv(self, other: Self) -> bool {
            self.ward() == other.ward()
                && self.val_before() == other.val_before()
                && self.val_after() == other.val_after()
        }

        #[requires(!(*self).shot())]
        #[requires(self.ward() == *(*own).ward())]
        #[ensures((*self).hist_inv(^self))]
        #[ensures((^self).shot())]
        #[ensures((*own).ward() == (^own).ward())]
        #[ensures(*(*own).val() == (*self).val_before())]
        #[ensures(*(^own).val() == (*self).val_after())]
        #[check(ghost)]
        #[trusted]
        #[allow(unused_variables)]
        pub fn shoot(&mut self, own: &mut Perm<Bag>) {
            panic!("Should not be called outside ghost code")
        }
    }

    impl Bag {
        #[trusted]
        #[ensures(*result.1.ward() == result.0)]
        #[ensures(*result.1.val() == FSet::empty())]
        pub fn create() -> (Bag, Ghost<Box<Perm<Bag>>>) {
            todo!()
        }

        #[trusted]
        #[requires(perm.ward() == self)]
        #[ensures(perm.ward() == (^perm).ward())]
        #[ensures(*(^perm).val() == perm.val().insert(x))]
        pub fn nonatomic_push(&self, perm: Ghost<&mut Perm<Bag>>, x: i32) {
            let _ = (perm, x);
            todo!()
        }

        #[requires(forall<c: &mut Committer>
             !c.shot() ==> c.ward() == *self ==> c.val_after() == c.val_before().insert(x) ==>
             f.precondition((c,)) && (f.postcondition_once((c,), ()) ==> (^c).shot())
        )]
        #[ensures(exists<c: &mut Committer>
             !c.shot() && c.ward() == *self && c.val_after() == c.val_before().insert(x) &&
             f.postcondition_once((c,), ())
         )]
        #[trusted]
        #[allow(unused_variables)]
        pub fn atomic_push<F>(&self, x: i32, f: Ghost<F>)
        where
            F: FnGhost + FnOnce(&mut Committer),
        {
            todo!()
        }

        #[trusted]
        #[requires(perm1.ward() == self && perm2.ward() == other)]
        #[ensures((^perm1).ward() == self && (^perm2).ward() == other)]
        #[ensures(*(^perm1).val() == FSet::empty())]
        #[ensures(*(^perm2).val() == (*perm2).val().union(*(*perm1).val()))]
        pub fn transfer(
            &self,
            other: &Self,
            perm1: Ghost<&mut Perm<Bag>>,
            perm2: Ghost<&mut Perm<Bag>>,
        ) {
            let _ = (other, perm1, perm2);
            todo!()
        }

        #[trusted]
        #[requires(perm.ward() == self)]
        #[ensures(result@ == *perm.val())]
        pub fn iter<'a>(&'a self, perm: Ghost<&'a Perm<Bag>>) -> BagIter<'a> {
            BagIter(self, perm)
        }

        #[trusted]
        #[requires(perm.ward() == self)]
        #[ensures((^perm).ward() == perm.ward())]
        #[ensures(*(^perm).val() == FSet::empty())]
        pub fn clear(&self, perm: Ghost<&mut Perm<Bag>>) {
            let _ = perm;
            todo!()
        }
    }

    #[opaque]
    pub struct BagIter<'a>(#[allow(unused)] &'a Bag, Ghost<&'a Perm<Bag>>);

    impl View for BagIter<'_> {
        type ViewTy = FSet<i32>;

        #[logic(opaque)]
        fn view(self) -> Self::ViewTy {
            dead
        }
    }

    impl<'a> Iterator for BagIter<'a> {
        type Item = i32;

        #[trusted]
        #[ensures(match result {
            None => self.completed(),
            Some(v) => (*self).produces(Seq::singleton(v), ^self),
        })]
        fn next(&mut self) -> Option<Self::Item> {
            todo!()
        }
    }

    impl<'a> IteratorSpec for BagIter<'a> {
        #[logic(prophetic, open)]
        fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
            pearlite! {
                (forall<x> self@.contains(x) == (o@.contains(x) || exists<j> 0 <= j && j < visited.len() && visited[j] == x)) &&
                (forall<i> 0 <= i && i < visited.len() ==> !o@.contains(visited[i])) &&
                (forall<i, j> 0 <= i && i < j && j < visited.len() ==> visited[i] != visited[j])
            }
        }

        #[logic(prophetic, open)]
        fn completed(&mut self) -> bool {
            pearlite! {
                self@ == FSet::empty() && *self == ^self
            }
        }

        #[logic(law)]
        #[trusted]
        #[ensures(self.produces(Seq::empty(), self))]
        fn produces_refl(self) {}

        #[logic(law)]
        #[trusted]
        #[requires(a.produces(ab, b))]
        #[requires(b.produces(bc, c))]
        #[ensures(a.produces(ab.concat(bc), c))]
        fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
    }
}

use bag::*;

/// The number of buckets `n` is an extra argument to enable stating the post.
#[trusted]
#[logic(opaque)]
#[ensures(0usize <= result && result < n)]
pub fn f_(i: usize, x: i32, n: usize) -> usize {
    dead
}

#[trusted]
#[ensures(result == f_(i, x, n))]
pub fn f(i: usize, x: i32, n: usize) -> usize {
    let _ = (i, x, n);
    todo!()
}

#[logic]
pub fn valid_wards(s: Seq<(Bag, Ghost<Box<Perm<Bag>>>)>) -> bool {
    pearlite! {
        forall<i> 0 <= i && i < s.len() ==> *s[i].1.ward() == s[i].0
    }
}

declare_namespace! { BAGS }

struct SharedBagsInv {
    next_shared_perm: Seq<Box<Perm<Bag>>>,
}

impl Protocol for SharedBagsInv {
    type Public = Seq<Bag>;

    #[logic(inline)]
    fn protocol(self, s: Seq<Bag>) -> bool {
        pearlite! {
            self.next_shared_perm.len() == s.len() &&
            forall<i> 0 <= i && i < s.len() ==> *self.next_shared_perm[i].ward() == s[i]
        }
    }
}

#[requires(valid_wards(cur@))]
#[requires(cur@.len() < usize::MAX@)]
pub fn compute(mut cur: Vec<(Bag, Ghost<Box<Perm<Bag>>>)>, k: u32) {
    #[allow(unused)]
    let n = snapshot!(cur@.len());

    let mut next_private = vec![];
    let mut next_shared: Vec<Bag> = vec![];
    let mut next_shared_perm: Ghost<Seq<Box<Perm<Bag>>>> = Seq::new();

    #[invariant(valid_wards(next_private@))]
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> *next_shared_perm[i].ward() == next_shared@[i])]
    #[invariant(next_private@.len() == produced.len())]
    #[invariant(next_shared@.len() == produced.len())]
    #[invariant(next_shared_perm.len() == produced.len())]
    for _ in 0..cur.len() {
        next_private.push(Bag::create());
        let (sh, p) = Bag::create();
        next_shared.push(sh);
        ghost! { next_shared_perm.push_back_ghost(p.into_inner()); };
    }

    #[invariant(valid_wards(cur@))]
    #[invariant(valid_wards(next_private@))]
    #[invariant(forall<i> 0 <= i && i < *n ==> *next_shared_perm[i].ward() == next_shared@[i])]
    #[invariant(cur@.len() == *n)]
    #[invariant(next_private@.len() == *n)]
    #[invariant(next_shared@.len() == *n)]
    #[invariant(next_shared_perm.len() == *n)]
    for _ in 0..k {
        let inv = AtomicInvariantSC::new(
            ghost!(SharedBagsInv {
                next_shared_perm: next_shared_perm.into_inner()
            }),
            snapshot!(next_shared@),
            snapshot!(BAGS()),
        );

        thread::scope(|s| {
            let mut handles: Vec<ScopedJoinHandle<_>> = vec![];
            let mut i = 0;

            #[allow(unused)]
            let next_private0 = snapshot!(next_private);
            let inv = &inv;

            #[invariant(i@ == produced.len() && handles@.len() == produced.len())]
            #[invariant(forall<i> 0 <= i && i < produced.len() && handles@[i].valid_result(()) ==> {
                let p = produced[i];
                (^p).0 == *(^p).1.ward()
            })]
            for p in next_private.iter_mut() {
                proof_assert!(*p == next_private0[produced.len() - 1]);
                let cur = &cur;
                let next_shared = &next_shared;
                let h = s.spawn(move |mut tokens| {
                    let (bag, perm) = &cur[i];
                    #[invariant(p.0 == *p.1.ward())]
                    #[invariant(forall<ns> tokens.contains(ns))]
                    for x in bag.iter(ghost! { &*perm }) {
                        let tokens = ghost!(tokens.reborrow());
                        let j = f(i, x, cur.len());
                        if i == j {
                            p.0.nonatomic_push(ghost!(&mut *p.1), x);
                        } else {
                            next_shared[j].atomic_push(
                                x,
                                ghost! { |c: &mut Committer| {
                                    inv.open(tokens.into_inner(), |inv: &mut SharedBagsInv| {
                                        c.shoot(&mut *inv.next_shared_perm[*Int::new(j as i128)]);
                                    })
                                }},
                            );
                        }
                    }
                });
                handles.push(h);
                i += 1
            }

            #[invariant(forall<i> 0 <= i && i < produced.len() ==> produced[i].valid_result(()))]
            for h in handles {
                h.join_unwrap();
            }
        });

        next_shared_perm = ghost!(inv.into_inner().into_inner().next_shared_perm);

        thread::scope(|s| {
            let mut handles: Vec<ScopedJoinHandle<_>> = vec![];
            let cur = &mut cur;
            let next_private = &mut next_private;
            let next_shared = &next_shared;
            let mut next_shared_perm = ghost!(next_shared_perm.as_muts());

            #[allow(unused)]
            let cur0 = snapshot!(cur);
            #[allow(unused)]
            let next_private0 = snapshot!(next_private);
            #[allow(unused)]
            let next_shared_perm0 = snapshot!(next_shared_perm);

            #[invariant(handles@.len() == produced.len())]
            #[invariant(forall<i> 0 <= i && i < produced.len() && handles@[i].valid_result(()) ==> {
                let ((c, p), sh) = produced[i];
                (^c).0 == *(^c).1.ward() &&
                (^p).0 == *(^p).1.ward() &&
                sh == (^next_shared_perm0[i]).ward()
            })]
            #[invariant(next_shared_perm.len() + produced.len() == cur0@.len())]
            #[invariant(forall<i> 0 <= i && i < next_shared_perm.len() ==> next_shared_perm[i] == next_shared_perm0[i + produced.len()])]
            #[invariant(forall<i> 0 <= i && i < produced.len() ==> ^produced[i].0.0 == (^cur0)[i] && ^produced[i].0.1 == (^next_private0)[i])]
            for ((c, p), sh) in { cur }.iter_mut().zip(next_private).zip(next_shared) {
                proof_assert!(*c == cur0[produced.len() - 1]);
                proof_assert!(*p == next_private0[produced.len() - 1]);
                proof_assert!(*sh == next_shared[produced.len() - 1]);
                let shp = ghost!(&mut **next_shared_perm.pop_front_ghost().unwrap());

                let h = s.spawn(move |_| {
                    c.0.clear(ghost!(&mut c.1));
                    p.0.transfer(&c.0, ghost!(&mut *p.1), ghost!(&mut *c.1));
                    sh.transfer(&c.0, shp, ghost!(&mut *c.1));
                });
                handles.push(h)
            }

            #[invariant(forall<i> 0 <= i && i < produced.len() ==> produced[i].valid_result(()))]
            for h in handles {
                h.join_unwrap();
            }
        })
    }
}
