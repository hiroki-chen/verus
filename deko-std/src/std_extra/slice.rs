use core::cmp::Ordering;
use core::slice::SliceIndex;

use vstd::prelude::*;
use vstd::std_specs::cmp::OrdSpec;

use crate::cmp::is_sorted_spec;
use crate::WellFormed;

verus! {

pub assume_specification[ core::str::from_utf8 ](_0: &[u8]) -> core::result::Result<
    &str,
    core::str::Utf8Error,
>
;

pub assume_specification<P>[ str::contains ](_0: &str, _1: P) -> bool where
    P: core::str::pattern::Pattern,

;

pub assume_specification<P>[ str::starts_with ](_0: &str, _1: P) -> bool where
    P: core::str::pattern::Pattern,

;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCStr(pub core::ffi::CStr);

pub assume_specification[ core::ffi::CStr::to_str ](_0: &core::ffi::CStr) -> core::result::Result<
    &str,
    core::str::Utf8Error,
>
;

pub assume_specification[ core::ffi::CStr::from_bytes_until_nul ](
    _0: &[u8],
) -> core::result::Result<&core::ffi::CStr, core::ffi::FromBytesUntilNulError>
;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUtf8Error(core::str::Utf8Error);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFromBytesUntilNulError(core::ffi::FromBytesUntilNulError);

impl<V: WellFormed, const N: usize> WellFormed for [V; N] {
    open spec fn wf(&self) -> bool {
        slice_wf(self@)
    }
}

impl<'a, V: WellFormed> WellFormed for &'a [V] {
    open spec fn wf(&self) -> bool {
        slice_wf(self@)
    }
}

pub open spec fn slice_wf<T: WellFormed>(s: Seq<T>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).wf()
}

pub assume_specification<T, U, const N: usize>[ <[T; N] as core::cmp::PartialEq<[U; N]>>::eq ](
    _0: &[T; N],
    _1: &[U; N],
) -> bool where T: core::cmp::PartialEq<U>
;

pub assume_specification<T>[ <[T]>::first ](s: &[T]) -> (r: Option<&T>)
    ensures
        s.len() == 0 ==> r == Option::<&T>::None,
        s.len() > 0 ==> r == Option::Some(&s@[0]),
;

pub assume_specification[ core::primitive::str::as_bytes ](s: &str) -> (r: &[u8])
    ensures
        r@ =~= s@.map_values(|v| v as u8),
;

pub assume_specification<P: core::str::pattern::Pattern>[ core::primitive::str::trim_end_matches ](
    s: &str,
    p: P,
) -> (r: &str) where
    for <'a><P as core::str::pattern::Pattern>::Searcher<'a>: core::str::pattern::ReverseSearcher<
        'a,
    >,

;

pub assume_specification[ <core::primitive::str as PartialEq>::eq ](s1: &str, s2: &str) -> (r: bool)
    ensures
        r <==> s1@ =~= s2@,
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

/// Returns the index of the partition point according to the given predicate
/// (the index of the first element of the second partition).
///
/// The slice is assumed to be partitioned according to the given predicate.
/// This means that all elements for which the predicate returns true are at
/// the start of the slice and all elements for which the predicate returns
/// false are at the end.
pub assume_specification<T, F>[ <[T]>::partition_point ](s: &[T], f: F) -> (r: usize) where
    F: FnMut(&T) -> bool,

    requires
        forall|i: int| #![trigger s@[i]] 0 <= i < s@.len() as int ==> f.requires((&s@[i],)),
    ensures
        0 <= r <= s.len(),
        forall|i: int| 0 <= i < r as int ==> f.ensures((#[trigger] &s@[i],), true),
        forall|i: int| r as int <= i < s.len() ==> f.ensures((#[trigger] &s@[i],), false),
;

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
