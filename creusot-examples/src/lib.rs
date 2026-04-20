// disable "unused ..." warnings when not using creusot, for things that are
// used in specifications, which are erased when not running creusot
// XXX could we do better?
#![cfg_attr(not(creusot), allow(unused_variables))]

pub mod binary_search;
pub mod borrows;
pub mod datastructures;
pub mod knapsack;
pub mod knuth_shuffle;
pub mod lists;
pub mod misc;
pub mod sorting;
