//! Challenge 2 of VerifyThis 2025
//!
//! https://verifythis.github.io/onsite/archive/2025/

#[cfg(creusot)]
use creusot_std::logic::such_that;
use creusot_std::{ghost::perm::Perm, prelude::*};

pub struct Node {
    next: *const Node,
}

pub struct List {
    head: *const Node,
    perms: Ghost<Seq<Box<Perm<*const Node>>>>,
}

impl Invariant for List {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            if self.perms.len() == 0 {
                self.head.is_null_logic()
            } else {
                self.head == *self.perms[0].ward()
                    && (forall<i> 0 <= i && i < self.perms.len() - 1 ==>
                        self.perms[i].val().next == *self.perms[i+1].ward())
                    && self.perms[self.perms.len() - 1].val().next.is_null_logic()
            }
        }
    }
}

impl List {
    #[logic]
    pub fn len_logic(self) -> Int {
        (*self.perms).len()
    }

    #[logic]
    pub fn elems(self) -> Seq<*const Node> {
        pearlite! {
            (*self.perms).map(|p: Box<Perm<*const Node>>| *p.ward())
        }
    }
}

/// The function we want to verify, for comparison with the verified version...
#[trusted]
pub unsafe fn remove_better(l: &mut List, toremove: *const Node) {
    let mut p = &mut l.head;
    while *p != toremove {
        p = &mut (unsafe { &mut *(*p as *mut Node) as &mut Node }).next;
    }
    *p = unsafe { &*toremove as &Node }.next;
}

#[check(terminates)]
#[erasure(remove_better)]
#[requires(l.len_logic() > 0)]
#[requires(exists<x: Int> 0 <= x && x < l.len_logic() && toremove == l.elems()[x])]
#[ensures({
    let x = such_that(|x: Int| 0 <= x && x < l.len_logic() && toremove == l.elems()[x]);
    (^l).elems() == l.elems().removed(x)
})]
#[ensures(*result.ward() == toremove)]
pub unsafe fn remove_better_verified(
    l: &mut List,
    toremove: *const Node,
) -> Ghost<Box<Perm<*const Node>>> {
    let _x =
        snapshot! { such_that(|x: Int| 0 <= x && x < l.len_logic() && toremove == l.elems()[x]) };
    let x_perm = ghost! { l.perms.remove(*_x.into_ghost()) };
    let mut mut_perms = ghost! { l.perms.as_muts() };
    let _mut_perms = snapshot! { mut_perms };
    ghost! {
        if *_x.into_ghost() != 0int {
            mut_perms[0int].disjoint_lemma(&x_perm);
        }
    };

    let mut p = &mut l.head;

    let _head = snapshot! { p };
    let mut _i = snapshot! { 0 };

    #[variant(mut_perms.len())]
    #[invariant(0 <= *_i)]
    #[invariant(*mut_perms == _mut_perms[*_i..])]
    #[invariant(*p != toremove ==> *_i < *_x && *p == *_mut_perms[*_i].ward())]
    #[invariant(*p == toremove ==> *_i == *_x)]
    #[invariant(0 == *_i ==> ^*_head == ^p)]
    #[invariant(0 < *_i
        ==> ^*_head == *(^_mut_perms[0]).ward()
        && (*_mut_perms[*_i - 1]).ward() == (^_mut_perms[*_i - 1]).ward()
        && (*_mut_perms[*_i - 1]).val().next == *p
        && (^_mut_perms[*_i - 1]).val().next == ^p
    )]
    #[invariant(forall<i> 0 <= i && i < *_i - 1
        ==> (*_mut_perms[i]).ward() == (^_mut_perms[i]).ward()
        && (*_mut_perms[i]).val() == (^_mut_perms[i]).val())]
    while *p != toremove {
        let p_perm = ghost! { &mut **mut_perms.pop_front_ghost().unwrap() };

        p = &mut (unsafe { Perm::as_mut(*p as *mut Node, p_perm) }).next;

        ghost! {
            _i = snapshot! { *_i + 1 };
            if *snapshot! { *_i < *_x }.into_ghost() {
                mut_perms[0int].disjoint_lemma(&x_perm)
            }
        };
    }

    proof_assert! { forall<i> *_x <= i && i < _mut_perms.len() ==> ^_mut_perms[i] == ^mut_perms[i - *_x] }

    *p = unsafe { Perm::as_ref(toremove, ghost! { &**x_perm }) }.next;

    x_perm
}
