use vstd::prelude::*;

verus! {

pub assume_specification<T>[ core::mem::ManuallyDrop::<T>::new ](value: T) -> (out:
    core::mem::ManuallyDrop<T>)
;

} // verus!
