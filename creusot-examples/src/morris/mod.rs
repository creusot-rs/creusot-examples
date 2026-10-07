mod morris;

pub use morris::{Tree, TreeIter};

#[allow(unused)]
#[cfg_attr(not(creusot), test)]
fn test() {
    use creusot_std::prelude::*;

    let t1 = Tree::singleton(1);
    let t3 = Tree::singleton(3);
    let t123 = Tree::merge_with(t1, 2, t3);
    proof_assert!(t123@ == seq![1i32, 2i32, 3i32]);

    let mut iter = t123.iter();
    assert!(*iter.next().unwrap() == 1);
    assert!(*iter.next().unwrap() == 2);
    let four = iter.next().unwrap();
    assert!(*four == 3);
    *four = 4;
    assert!(iter.next().is_none());

    let tree = iter.into_tree();
    proof_assert!(tree@ == seq![1i32, 2i32, 4i32]);
}
