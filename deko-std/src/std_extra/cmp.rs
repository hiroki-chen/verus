use core::alloc::Allocator;
use core::cmp::Ordering;

use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};

verus! {

// Refactor: Perhaps these definitions should be moved to deko_std.
pub proof fn lemma_cmp_pivot_monotonic(a: u64, b: u64, pivot: u64)
    requires
        a <= b,
    ensures
        a.cmp_spec(&pivot).cmp_spec(&b.cmp_spec(&pivot)) != Ordering::Greater,
{
    // Case analysis - Verus may prove automatically, or:
    if a < pivot {
        assert(a.cmp_spec(&pivot) == Ordering::Less);
        // b.cmp_spec(&pivot) is Less, Equal, or Greater - all >= Less in ordering

    } else if a == pivot {
        assert(a.cmp_spec(&pivot) == Ordering::Equal);
        if b < pivot {
            assert(false);  // contradicts a <= b
        }
        // b.cmp_spec(&pivot) is Equal or Greater - both >= Equal

    } else {
        assert(a.cmp_spec(&pivot) == Ordering::Greater);
        assert(b > pivot);  // since a <= b and a > pivot
        assert(b.cmp_spec(&pivot) == Ordering::Greater);
    }
}

pub open spec fn is_sorted_spec<T: PartialOrd>(s: vstd::seq::Seq<T>) -> bool {
    forall|i: int, j: int|
        #![trigger s[i], s[j]]
        0 <= i && i < j && j < s.len() ==> s[i].partial_cmp_spec(&s[j]) == Some(Ordering::Less)
            || s[i].partial_cmp_spec(&s[j]) == Some(Ordering::Equal)
}

pub open spec fn is_sorted_by_spec<'a, T: 'a, F>(s: vstd::seq::Seq<T>, f: F) -> bool where
    F: FnMut(&'a T, &'a T) -> Ordering,
 {
    forall|i: int, j: int|
        #![trigger s[i], s[j]]
        0 <= i && i < j && j < s.len() ==> forall|ord: Ordering|
            f.ensures((&s[i], &s[j]), ord) ==> ord != Ordering::Greater
}

pub assume_specification<T: PartialOrd>[ <[T]>::is_sorted ](s: &[T]) -> (r: bool)
    returns
        is_sorted_spec(s@),
;

pub open spec fn binary_search_spec<'a, T: 'a>(
    s: vstd::seq::Seq<T>,
    x: &T,
    r: Result<usize, usize>,
) -> bool where T: Ord {
    match r {
        Ok(idx) => {
            &&& 0 <= idx < s.len()
            &&& s[idx as int] == *x
        },
        Err(idx) => {
            &&& 0 <= idx <= s.len()
            &&& (idx == s.len() || s[idx as int] != *x)
            &&& (idx == 0 || s[idx - 1] != *x)
        },
    }
}

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
        binary_search_spec(s@, x, r),
;

/// Note that this function is used in pre-condition so we keep `f.ensures ==> x`.
pub open spec fn comparator_consistent_spec<'a, T: 'a, F>(s: vstd::seq::Seq<T>, f: F) -> bool where
    F: FnMut(&'a T) -> Ordering,
 {
    forall|i: int, j: int, ord1: Ordering, ord2: Ordering|
        #![trigger s[i], s[j], f.ensures((&s[i],), ord1), f.ensures((&s[j],), ord2)]
        0 <= i < j < s.len() && f.ensures((&s[i],), ord1) && f.ensures((&s[j],), ord2)
            ==> ord1.cmp_spec(&ord2) != Ordering::Greater
}

pub open spec fn binary_search_by_spec<'a, T: 'a, F>(
    s: vstd::seq::Seq<T>,
    f: F,
    r: Result<usize, usize>,
) -> bool where F: FnMut(&'a T) -> Ordering {
    match r {
        Ok(idx) => {
            &&& 0 <= idx < s.len()
            &&& f.ensures((&s[idx as int],), Ordering::Equal)
        },
        Err(idx) => {
            &&& 0 <= idx <= s.len()
            &&& forall|i: int| 0 <= i < idx ==> f.ensures((#[trigger] &s[i],), Ordering::Less)
            &&& forall|i: int|
                idx <= i < s.len() ==> f.ensures((#[trigger] &s[i],), Ordering::Greater)
        },
    }
}

/// The comparator function should return an order code that indicates whether its argument is
/// [`Ordering::Less`], [`Ordering::Equal`], or [`Ordering::Greater`]
/// the desired target. If the slice is not sorted or if the comparator function does not
/// implement an order consistent with the sort order of the underlying slice, the returned
/// result is unspecified and meaningless.
///
/// If the value is found then [`Result::Ok`] is returned, containing the index of the matching
/// element. If there are multiple matches, then any one of the matches could be returned.
/// The index is chosen deterministically, but is subject to change in future versions of Rust.
/// If the value is not found then [`Result::Err`] is returned, containing the index where a matching
/// element could be inserted while maintaining sorted order.
pub assume_specification<'a, T, F>[ <[T]>::binary_search_by ](s: &'a [T], mut f: F) -> (r: Result<
    usize,
    usize,
>) where F: FnMut(&'a T) -> Ordering
    requires
        comparator_consistent_spec(s@, f),
        forall|i: int| #![trigger s@[i]] 0 <= i < s@.len() as int ==> f.requires((&s@[i],)),
    ensures
        binary_search_by_spec(s@, f, r),
;

} // verus!
