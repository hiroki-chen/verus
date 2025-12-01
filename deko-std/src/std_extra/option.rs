use vstd::prelude::*;

verus! {

pub assume_specification<T>[ core::option::Option::<T>::replace ](
    opt: &mut Option<T>,
    value: T,
) -> (r: Option<T>)
    ensures
        opt == Some(value),
        match *old(opt) {
            None => r == None::<T>,
            Some(old_value) => r == Some(old_value),
        },
;

} // verus!
