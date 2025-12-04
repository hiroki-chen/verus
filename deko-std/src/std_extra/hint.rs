use vstd::prelude::*;

verus! {

pub assume_specification[ core::hint::unlikely ](b: bool) -> (r: bool)
    ensures
        r == b,
;

pub assume_specification[ core::hint::likely ](b: bool) -> (r: bool)
    ensures
        r == b,
;

pub assume_specification[ core::hint::spin_loop ]()
;

} // verus!
