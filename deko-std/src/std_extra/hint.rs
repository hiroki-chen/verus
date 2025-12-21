use vstd::prelude::*;

verus! {

pub assume_specification[ core::hint::unlikely ](b: bool) -> (r: bool)
    ensures
        r == b,
    opens_invariants none
    no_unwind
;

pub assume_specification[ core::hint::likely ](b: bool) -> (r: bool)
    ensures
        r == b,
    opens_invariants none
    no_unwind
;

pub assume_specification[ core::hint::spin_loop ]()
    opens_invariants none
    no_unwind
;

} // verus!
