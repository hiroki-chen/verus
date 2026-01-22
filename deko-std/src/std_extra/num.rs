use vstd::prelude::*;

verus! {

pub assume_specification[ isize::abs ](n: isize) -> (r: isize)
    ensures
        r as int == isize_abs(n as int),
;

pub open spec fn isize_abs(n: int) -> int {
    if n >= 0 {
        n
    } else {
        -n
    }
}

} // verus!
