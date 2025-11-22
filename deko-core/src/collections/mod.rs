//! This module implements more high-level APIs for allocating memories from the heap.
//!
//! The reason why we need this module is that we implement the heap in a buddy allocator
//! that returns raw memories. However, in many cases, we will need to allocate pages.
use core::alloc::Allocator;

use vstd::prelude::*;

use crate::mm::frame_allocator::DekoAllocatorApi;

verus! {

/// A type alias for a vector that uses the Deko page frame allocator as its allocator.
pub type Vec<T> = alloc::vec::Vec<T, DekoAllocatorApi>;

/// A type alias for a vector declaration that uses the Deko page frame allocator as its allocator.
pub type VecDeque<T> = alloc::collections::vec_deque::VecDeque<T, DekoAllocatorApi>;

pub assume_specification<T, A: Allocator>[ alloc::vec::Vec::<T, A>::new_in ](alloc: A) -> (v:
    alloc::vec::Vec<T, A>)
    ensures
        v@ == Seq::<T>::empty(),
;

} // verus!
/// Creates a [`Vec`] containing the arguments.
///
/// `vec!` allows `Vec`s to be defined with the same syntax as array expressions.
/// There are two forms of this macro:
#[macro_export]
macro_rules! vec {
    ($($x:expr),* $(,)?) => {
        {
            let allocator = DekoAllocatorApi {  };
            let mut temp_vec = $crate::collections::Vec::new_in(allocator);
            $(
                temp_vec.push($x);
            )*
            temp_vec
        }
    };
    () => {
        {
            let allocator = DekoAllocatorApi {  };
            $crate::collections::Vec::new_in(allocator)
        }
    };
}
