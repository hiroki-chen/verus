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

} // verus!
