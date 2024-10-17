// Used by:
// sorting/heap_sort.rs
#![feature(type_ascription)]

// Used by:
// datastructures/red_black_tree.rs
#![feature(box_patterns)]

// Required for contracts annotations.
// (The attribute are enabled by `cargo creusot` but we need to add them to be
//  able to run `cargo build` as well.)
#![cfg_attr(not(creusot),feature(stmt_expr_attributes,proc_macro_hygiene))]

// Used by:
// misc/ite_normalize.rs
// misc/hillel.rs
#![feature(allocator_api)]

// disable "unused ..." warnings when not using creusot, for things that are
// used in specifications, which are erased when not running creusot
// XXX could we do better?
#![cfg_attr(not(creusot),allow(unused_imports,dead_code,unused_variables,unused_assignments))]

pub mod binary_search;
pub mod borrows;
pub mod datastructures;
pub mod knapsack;
pub mod knuth_shuffle;
pub mod lists;
pub mod misc;
pub mod sorting;
