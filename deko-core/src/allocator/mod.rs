//! This module implements more high-level APIs for allocating memories from the heap.
//!
//! The reason why we need this module is that we implement the heap in a buddy allocator
//! that returns raw memories. However, in many cases, we will need to allocate pages.
use vstd::prelude::*;

use crate::mm::paging::Page;

pub(crate) mod heap;

verus! {


} // verus!
