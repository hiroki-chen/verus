//! This module implements more high-level APIs for allocating memories from the heap.
//!
//! The reason why we need this module is that we implement the heap in a buddy allocator
//! that returns raw memories. However, in many cases, we will need to allocate pages.
use core::alloc::Allocator;

use vstd::prelude::*;
use vstd::std_specs::cmp::PartialOrdSpec;

use crate::mm::frame_allocator::DekoAllocatorApi;

verus! {

/// A type alias for a vector that uses the Deko page frame allocator as its allocator.
///
/// For common slice-like functions please call [`Vec::as_slice`] to get a slice reference which
/// guarantees that the underlying [`View`] of the vector will be the same as `[T]`
///
/// # Special Notes
///
/// Some lemmas and proofs imported directly from `vstd` will broken as [`alloc::vec::Vec<T>`] is
/// _not_ the same thing as [`alloc::vec::Vec<T, A>`].
pub type Vec<T> = alloc::vec::Vec<T, DekoAllocatorApi>;

/// A type alias for a vector declaration that uses the Deko page frame allocator as its allocator.
pub type VecDeque<T> = alloc::collections::vec_deque::VecDeque<T, DekoAllocatorApi>;

pub broadcast proof fn axiom_spec_len<T, A: Allocator>(v: &alloc::vec::Vec<T, A>)
    ensures
        #[trigger] vstd::std_specs::vec::spec_vec_len(v) == v@.len(),
{
    admit();
}

pub open spec fn is_sorted_spec<T: PartialOrd>(s: vstd::seq::Seq<T>) -> bool {
    forall|i: int, j: int|
        #![trigger s[i], s[j]]
        0 <= i && i < j && j < s.len() ==> s[i].partial_cmp_spec(&s[j]) == Some(
            core::cmp::Ordering::Less,
        )
}

pub assume_specification<T, A: Allocator>[ alloc::vec::Vec::<T, A>::new_in ](alloc: A) -> (v:
    alloc::vec::Vec<T, A>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T: PartialOrd>[ <[T]>::is_sorted ](s: &[T]) -> (r: bool)
    returns
        is_sorted_spec(s@),
;

/// Binary searches this slice for a given element.
/// If the slice is not sorted, the returned result is unspecified
/// and meaningless.
///
/// If the value is found then [`Result::Ok`] is returned, containing the
/// index of the matching element. If there are multiple matches, then
/// any one of the matches could be returned. The index is chosen
/// deterministically, but is subject to change in future versions of
/// Rust. If the value is not found then [`Result::Err`] is returned,
/// containing the index where a matching element could be inserted
/// while maintaining sorted order.
pub assume_specification<T: Ord>[ <[T]>::binary_search ](s: &[T], x: &T) -> (r: Result<
    usize,
    usize,
>)
    requires
        is_sorted_spec(s@),
    ensures
        match r {
            Ok(idx) => 0 <= idx < s@.len() && s@[idx as int] == *x,
            Err(idx) => 0 <= idx <= s@.len() && (idx == s@.len() || s@[idx as int] != *x) && (idx
                == 0 || s@[idx - 1] != *x),
        },
;

pub assume_specification<'a, T, F>[ <[T]>::binary_search_by ](s: &'a [T], mut f: F) -> (r: Result<
    usize,
    usize,
>) where F: FnMut(&'a T) -> core::cmp::Ordering
    requires
        forall|i: int| #![trigger s@[i]] 0 <= i < s@.len() as int ==> f.requires((&s@[i],)),
    ensures
        match r {
            Ok(idx) => 0 <= idx < s@.len(),
            Err(idx) => 0 <= idx <= s@.len(),  // other parts delayed.
        },
;

pub broadcast group group_vec_axioms {
    axiom_spec_len,
}

} // verus!
/// Creates a [`Vec`] containing the arguments.
///
/// `vec!` allows `Vec`s to be defined with the same syntax as array expressions.
/// There are two forms of this macro:
#[macro_export]
macro_rules! vec {
    ($($x:expr),* $(,)?) => {
        {
            let allocator = $crate::mm::frame_allocator::DekoAllocatorApi {  };
            let mut temp_vec = $crate::collections::Vec::new_in(allocator);
            $(
                temp_vec.push($x);
            )*
            temp_vec
        }
    };
    () => {
        {
            let allocator = $crate::mm::frame_allocator::DekoAllocatorApi {  };
            $crate::collections::Vec::new_in(allocator)
        }
    };
}
