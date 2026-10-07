#[cfg(creusot)]
use creusot_std::std::mem::size_of_logic;
use creusot_std::{ghost::Perm, logic::Mapping, prelude::*};

/// A binary tree.
///
/// No additional structure is ensured: values are not sorted, the tree is not balanced, etc.
pub struct Tree<T> {
    root: *const Node<T>,
    root_idx: Snapshot<Int>,
    permissions: Ghost<Seq<Perm<*const Node<T>>>>,
    children: Snapshot<Children>,
}

/// Information about the children in the tree.
///
/// It keeps the indices of the right/left (most) children of a given node.
/// If a node has no left (resp. right) child, `left[node] == node` and
/// `leftmost[node] == node` (resp right, rightmost).
#[cfg_attr(not(creusot), allow(dead_code))]
struct Children {
    len: Int,
    root: Int,
    /// Left child of a node
    left: Mapping<Int, Int>,
    /// Right child of a node
    right: Mapping<Int, Int>,
    /// Leftmost child of a node (left child taken until null)
    leftmost: Mapping<Int, Int>,
    /// Rightmost child of a node (right child taken until null)
    rightmost: Mapping<Int, Int>,
}

impl Children {
    #[logic]
    fn well_formed(self) -> bool {
        pearlite! {
            (self.len > 0 ==> 0 <= self.root && self.root < self.len && self.leftmost[self.root] == 0 && self.rightmost[self.root] == self.len - 1) &&
            forall<i> 0 <= i && i < self.len ==> self.well_formed_at(i)
        }
    }

    #[logic(inline)]
    fn well_formed_at(self, i: Int) -> bool {
        // No chaining operator :'(
        0 <= self.leftmost[i]
            && self.leftmost[i] <= self.left[i]
            && self.left[i] <= i
            && i <= self.right[i]
            && self.right[i] <= self.rightmost[i]
            && self.rightmost[i] < self.len
            && self.leftmost[self.left[i]] == self.leftmost[i]
            && self.rightmost[self.right[i]] == self.rightmost[i]
            && if self.left[i] == i {
                self.leftmost[i] == i
            } else {
                self.rightmost[self.left[i]] == i - 1
            }
            && if self.right[i] == i {
                self.rightmost[i] == i
            } else {
                self.leftmost[self.right[i]] == i + 1
            }
    }

    #[logic(inline)]
    fn well_formed_tree_at<T>(self, permissions: Seq<Perm<*const Node<T>>>, i: Int) -> bool {
        (if self.right[i] == i {
            permissions[i].val().right.is_null_logic()
        } else {
            permissions[i].val().right == *permissions[self.right[i]].ward()
        }) && if self.left[i] == i {
            permissions[i].val().left.is_null_logic()
        } else {
            permissions[i].val().left == *permissions[self.left[i]].ward()
        }
    }

    #[logic(inline)]
    fn well_formed_tree<T>(self, permissions: Seq<Perm<*const Node<T>>>, root: Int) -> bool {
        let len = permissions.len();
        self.well_formed()
            && self.len == len
            && self.root == root
            && pearlite! {
                forall<i> 0 <= i && i < len ==> self.well_formed_tree_at(permissions, i)
            }
    }
}

/// Internal representation of a tree node.
struct Node<T> {
    value: T,
    left: *const Node<T>,
    right: *const Node<T>,
}

impl<T> Invariant for Tree<T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        let len = self.permissions.len();
        size_of_logic::<Node<T>>() > 0
            && self
                .children
                .well_formed_tree(*self.permissions, *self.root_idx)
            && if self.root.is_null_logic() {
                len == 0
            } else {
                0 <= *self.root_idx
                    && *self.root_idx < len
                    && *self.permissions[*self.root_idx].ward() == self.root
            }
    }
}

/// Model for the tree: sequence of the elements, in infix order
impl<T> View for Tree<T> {
    type ViewTy = Seq<T>;

    #[logic]
    fn view(self) -> Seq<T> {
        self.permissions
            .map(|perm: Perm<*const Node<T>>| perm.val().value)
    }
}

impl<T> Tree<T> {
    /// Create a new empty tree.
    #[ensures(result@.len() == 0)]
    pub fn new() -> Self {
        Self {
            root: std::ptr::null(),
            root_idx: snapshot!(-1),
            permissions: Seq::new(),
            children: snapshot!(Children {
                len: 0,
                root: -1,
                left: |_| 0,
                right: |_| 0,
                leftmost: |_| 0,
                rightmost: |_| 0,
            }),
        }
    }

    /// Create a tree with one value.
    #[ensures(result@ == Seq::singleton(value))]
    pub fn singleton(value: T) -> Self {
        let (root, root_perm) = Perm::new(Node {
            value,
            left: std::ptr::null(),
            right: std::ptr::null(),
        });
        Self {
            root,
            root_idx: snapshot!(0),
            permissions: ghost! {
                let mut p = Seq::new().into_inner();
                p.push_back_ghost(root_perm.into_inner());
                p
            },
            children: snapshot!(Children {
                len: 1,
                root: 0,
                left: |_| 0,
                right: |_| 0,
                leftmost: |_| 0,
                rightmost: |_| 0,
            }),
        }
    }

    /// Merge two trees together, putting `value` in the middle.
    #[ensures(result@ == self@.push_back(value).concat(other@))]
    pub fn merge_with(self, value: T, other: Self) -> Self {
        let (root, root_perm) = Perm::new(Node {
            value,
            left: self.root,
            right: other.root,
        });
        let perms = snapshot!((self.permissions, root_perm, other.permissions));
        // program code ends here! Now for ghost code :)
        let (permissions, root_idx, children) = ghost! {
            let self_len = self.permissions.len_ghost();
            let root_idx = self_len;
            let mut perms = self.permissions.into_inner();
            perms.push_back_ghost(root_perm.into_inner());
            perms.extend(other.permissions.into_inner());
            let left_is_null = self.root.is_null();
            let right_is_null = other.root.is_null();

            let children = snapshot!(Children {
                len: perms.len(),
                root: root_idx,
                left:      |i| if i < self_len { self.children.left[i] }
                               else if i == self_len { if left_is_null { self_len } else { *self.root_idx } }
                               else { other.children.left[i - self_len - 1] + self_len + 1 },
                leftmost:  |i| if i < self_len { self.children.leftmost[i] }
                               else if i == self_len { 0 }
                               else { other.children.leftmost[i - self_len - 1] + self_len + 1 },
                right:     |i| if i < self_len { self.children.right[i] }
                               else if i == self_len { if right_is_null { self_len } else { self_len + 1 + *other.root_idx } }
                               else { other.children.right[i - self_len - 1] + self_len + 1 },
                rightmost: |i| if i < self_len { self.children.rightmost[i] }
                               else if i == self_len { perms.len() - 1 }
                               else { other.children.rightmost[i - self_len - 1] + self_len + 1 },
            });
            (perms, root_idx, children)
        }.split();

        // TODO: remove these assertions if possible
        proof_assert!(forall<i> 0 <= i && i < children.len ==> children.well_formed_at(i));
        proof_assert!(forall<i> 0 <= i && i < permissions.len() ==> permissions[i] == if i < perms.0.len() {
            perms.0[i]
        } else if i == perms.0.len() {
            *perms.1
        } else {
            perms.2[i - perms.0.len() - 1]
        });

        Self {
            root,
            root_idx: snapshot!(*root_idx),
            permissions,
            children: snapshot!(**children),
        }
    }

    /// Create an iterator over the values of this tree.
    #[ensures(result@ == self@)]
    #[ensures(*result.visited == 0)]
    pub fn iter(self) -> TreeIter<T> {
        TreeIter {
            curr_ptr: self.root,
            root_ptr: self.root,
            visited: snapshot!(0),
            curr: self.root_idx,
            children: self.children,
            loopbacks: snapshot!(Seq::empty()),
            permissions: self.permissions,
        }
    }
}

pub struct TreeIter<T> {
    /// Internal state of the iteration.
    curr_ptr: *const Node<T>,
    /// Original root pointer of the tree.
    ///
    /// Unchanged during iteration.
    root_ptr: *const Node<T>,
    /// Number of elements that we already returned.
    pub visited: Snapshot<Int>,
    /// Index of the permission for `curr` in `permissions`.
    curr: Snapshot<Int>,
    /// Information about the tree layout.
    ///
    /// Unchanged during iteration.
    children: Snapshot<Children>,
    /// Which elements loop back to their infix successor?
    loopbacks: Snapshot<Seq<Int>>,
    /// Ghost permissions: keep the ownership of the **full** tree.
    permissions: Ghost<Seq<Perm<*const Node<T>>>>,
}

impl<T> View for TreeIter<T> {
    type ViewTy = Seq<T>;

    /// The sequence of elements still to visit.
    #[logic]
    fn view(self) -> Seq<T> {
        self.permissions
            .map(|perm: Perm<*const Node<T>>| perm.val().value)
    }
}

impl<T> Invariant for TreeIter<T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        let len = self.permissions.len();
        size_of_logic::<Node<T>>() > 0
            && self.children.well_formed()
            && self.well_formed_permissions()
            && self.invariant_loopbacks()
            && if len == 0 {
                self.root_ptr.is_null_logic()
            } else {
                *self.permissions[self.root()].ward() == self.root_ptr
            }
            && if self.curr_ptr.is_null_logic() {
                *self.visited == len
            } else {
                0 <= *self.visited
                    && *self.visited <= *self.curr
                    && *self.curr < len
                    // Either we finished visiting the left tree, or we are about to go into it.
                    && (self.visited == self.curr || *self.visited == self.children.leftmost[*self.curr])
                    && *self.permissions[*self.curr].ward() == self.curr_ptr
            }
    }
}

/// Alternative spec for `Seq::push_front`, which seems easier for this proof.
///
/// This should be the same as why3's, and yet...
#[logic]
#[ensures(result.len() == s.len() + 1)]
#[ensures(result[0] == item)]
#[ensures(forall<i> 0 <= i && i < s.len() ==>
    result[i + 1] == s[i]
)]
fn push_front_indexed<T>(s: Seq<T>, item: T) -> Seq<T> {
    s.push_front(item)
}

/// Alternative spec for `Seq::pop_front`, which seems easier for this proof.
///
/// This should be the same as why3's, and yet...
#[logic(opaque)]
#[requires(s.len() > 0)]
#[ensures(result.len() == s.len() - 1)]
#[ensures(forall<i> 0 <= i && i < result.len() ==>
    result[i] == s[i + 1]
)]
fn pop_front_indexed<T>(s: Seq<T>) -> Seq<T> {
    s.pop_front()
}

impl<T> TreeIter<T> {
    #[logic(inline)]
    fn root(self) -> Int {
        self.children.root
    }

    /// Specifies how the pointers in `self.permissions` are laid out.
    #[logic(inline)]
    fn well_formed_permissions(self) -> bool {
        pearlite! {
            self.children.len == self.permissions.len() && self.children.root == self.root() &&
            forall<i> 0 <= i && i < self.permissions.len() ==>
            (if self.children.right[i] == i {
                if self.loopbacks.contains(i) {
                    i < self.permissions.len() - 1 && self.permissions[i].val().right == *self.permissions[i + 1].ward()
                } else {
                    self.permissions[i].val().right.is_null_logic()
                }
            } else {
                self.permissions[i].val().right == *self.permissions[self.children.right[i]].ward()
            }) && if self.children.left[i] == i {
                self.permissions[i].val().left.is_null_logic()
            } else {
                self.permissions[i].val().left == *self.permissions[self.children.left[i]].ward()
            }
        }
    }

    /// Characterizes the chain of loopbacks up to the root.
    #[logic(inline)]
    fn invariant_loopbacks(self) -> bool {
        let loopbacks = self.loopbacks;
        let curr = *self.curr;
        let visited = *self.visited;
        let last = self.permissions.len() - 1;
        let c = *self.children;

        pearlite! {
            // the first loopback
            (if visited == self.permissions.len() {
                loopbacks.len() == 0
            } else if visited == curr && c.left[curr] != curr {
                loopbacks.len() > 0 && loopbacks[0] == curr - 1
            } else {
                visited == c.leftmost[curr]
                    && if c.rightmost[curr] == last {
                        loopbacks.len() == 0
                    } else {
                        loopbacks.len() > 0 && loopbacks[0] == c.rightmost[curr]
                    }
            }) &&
            // the last loopback
            (loopbacks.len() > 0 ==> c.rightmost[loopbacks[loopbacks.len() - 1] + 1] == last) &&
            // generalities on loopbacks
            (forall<i> 0 <= i && i < loopbacks.len() ==>
                0 <= loopbacks[i] && loopbacks[i] < last &&
                c.right[loopbacks[i]] == loopbacks[i] &&
                c.rightmost[c.left[loopbacks[i] + 1]] == loopbacks[i]
            ) &&
            forall<i> 0 <= i && i < loopbacks.len() - 1 ==>
                c.rightmost[loopbacks[i] + 1] == loopbacks[i + 1]
        }
    }

    /// Lemma: characterize the case when we are at the end of the iteration.
    #[logic]
    #[requires(inv(self))]
    #[requires(!self.curr_ptr.is_null_logic())]
    #[requires(self.permissions.len() > 0)]
    #[requires(self.children.right[*self.curr] == *self.curr)]
    #[requires(!self.loopbacks.contains(*self.curr))]
    #[requires(self.loopbacks.len() == 0 ==> self.children.left[*self.curr] == *self.curr)]
    #[ensures(*self.visited == self.permissions.len() - 1)]
    fn current_is_last(self) {}

    /// Lemma: all loopbacks are in increasing order.
    #[logic]
    #[requires(inv(self))]
    #[requires(0 <= i && i < j && j < self.loopbacks.len())]
    #[ensures(self.loopbacks[i] < self.loopbacks[j])]
    #[variant(self.loopbacks.len() - i)]
    fn loopbacks_incr(self, i: Int, j: Int) {
        if j > i + 1 {
            self.loopbacks_incr(i + 1, j);
        }
    }

    /// Ghost lemma: check that the permissions at `i1` and `i2` are disjoint.
    #[check(ghost)]
    #[requires(0 <= *i1 && *i1 < *i2 && *i2 < perms.len())]
    #[ensures(^perms == *perms)]
    #[ensures(perms[*i1].ward() != perms[*i2].ward())]
    fn disjoint_indices(
        perms: &mut Ghost<Seq<Perm<*const Node<T>>>>,
        i1: Snapshot<Int>,
        i2: Snapshot<Int>,
    ) {
        ghost! {
            let (c, p) = &mut perms[(i1.into_ghost().into_inner(), i2.into_ghost().into_inner())];
            c.disjoint_lemma(p);
        };
    }

    #[check(terminates)]
    #[requires(*self.visited == self@.len())]
    #[ensures(result@ == self@)]
    pub fn into_tree(self) -> Tree<T> {
        Tree {
            root: self.root_ptr,
            root_idx: snapshot!(self.root()),
            permissions: self.permissions,
            children: self.children,
        }
    }

    /// Get the next element of this iterator.
    ///
    /// Note that the lifetimes will force you to drop the returned value before the
    /// next call to `next`.
    ///
    /// # Implementation
    ///
    /// This uses Morris's algorithm internally, meaning that:
    /// - time complexity is O(n).
    /// - Space complexity is O(1).
    #[ensures(match result {
        None => ^self == *self && *self.visited == self@.len(),
        Some(x) =>
            *self.visited < self@.len() &&
            (*self)@[*self.visited] == *x &&
            (^self)@ == (*self)@.set(*self.visited, ^x) &&
            *(^self).visited == *(*self).visited + 1,
    })]
    #[erasure(Self::erased_next)]
    pub fn next(&mut self) -> Option<&mut T> {
        // Helper macros to get references from pointers
        macro_rules! to_ref {
            ($e:expr, $i:expr) => {{
                unsafe {
                    Perm::as_ref(
                        $e,
                        ghost!({
                            let i: Snapshot<Int> = $i;
                            &self.permissions[*i.into_ghost()]
                        }),
                    )
                }
            }};
        }
        macro_rules! to_mut {
            ($e:expr, $i:expr) => {{
                unsafe {
                    Perm::as_mut(
                        $e.cast_mut(),
                        ghost!({
                            let i: Snapshot<Int> = $i;
                            &mut self.permissions[*i.into_ghost()]
                        }),
                    )
                }
            }};
        }

        if self.curr_ptr.is_null() {
            return None;
        }

        let curr = to_ref!(self.curr_ptr, self.curr);
        let mut pred_ptr = curr.left;
        let mut pred = snapshot!(self.children.left[*self.curr]);

        let this = snapshot!(self);
        let _ = snapshot!(Self::current_is_last);

        if !pred_ptr.is_null() {
            #[invariant(0 <= *pred && *pred < self.permissions.len())]
            #[invariant(*self.permissions[*pred].ward() == pred_ptr)]
            #[invariant(self.children.rightmost[*pred] == *self.curr - 1)]
            loop {
                let right = to_ref!(pred_ptr, pred).right;
                let new_pred: Snapshot<Int> = snapshot!(self.children.right[*pred]);
                if right.is_null() {
                    to_mut!(pred_ptr, pred).right = self.curr_ptr;
                    self.curr_ptr = to_ref!(self.curr_ptr, self.curr).left;

                    // update current position and loopbacks
                    ghost! {
                        self.curr = snapshot!(self.children.left[*self.curr]);
                        self.loopbacks = snapshot!(push_front_indexed(*self.loopbacks, *pred));
                    };

                    return self.next();
                } else if right == self.curr_ptr {
                    // Prove disjointness of `curr` and `right[pred]`, update loopbacks
                    ghost! {
                        let _ = snapshot!(Self::loopbacks_incr);
                        Self::disjoint_indices(&mut self.permissions, new_pred, self.curr);
                        self.loopbacks = snapshot!(pop_front_indexed(*self.loopbacks));
                        proof_assert!(
                            forall<i> 0 <= i && i < self.permissions.len() ==>
                            this.loopbacks.contains(i) == (i == *pred || self.loopbacks.contains(i))
                        );
                    };

                    to_mut!(pred_ptr, pred).right = std::ptr::null();
                    break;
                }
                pred_ptr = right;
                ghost! { pred = new_pred };
            }
        }

        let old_curr = snapshot!(*self.curr);
        // update current position
        ghost! {
            proof_assert!(self.visited == self.curr);
            self.curr = snapshot!(if *self.curr == self.permissions.len() - 1 {
                *self.curr
            } else if self.children.right[*self.curr] == *self.curr {
                *self.curr + 1
            } else {
                self.children.right[*self.curr]
            });
            self.visited = snapshot!(*self.visited + 1);
        };

        let curr = to_mut!(self.curr_ptr, old_curr);
        self.curr_ptr = curr.right;

        Some(&mut curr.value)
    }

    #[trusted]
    pub fn erased_next(&mut self) -> Option<&mut T> {
        if self.curr_ptr.is_null() {
            return None;
        }

        let curr = unsafe { &*self.curr_ptr };
        let mut pred = curr.left;

        if !pred.is_null() {
            loop {
                let right = unsafe { (&*pred).right };
                if right.is_null() {
                    unsafe { &mut *pred.cast_mut() }.right = self.curr_ptr;
                    self.curr_ptr = unsafe { &*self.curr_ptr }.left;
                    return self.erased_next();
                } else if right == self.curr_ptr {
                    unsafe { &mut *pred.cast_mut() }.right = std::ptr::null();
                    break;
                }
                pred = right;
            }
        }

        let curr = unsafe { &mut *self.curr_ptr.cast_mut() };
        self.curr_ptr = curr.right;
        Some(&mut curr.value)
    }
}
