use vstd::prelude::*;

verus! {

pub assume_specification<T, E, F: FnOnce(E) -> bool>[ core::result::Result::<T, E>::is_err_and ](
    res: core::result::Result<T, E>,
    f: F,
) -> (r: bool)
    ensures
        match res {
            core::result::Result::Err(e) => f.ensures((e,), r),
            core::result::Result::Ok(_) => r == false,
        },
;

} // verus!
