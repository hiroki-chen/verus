use vstd::prelude::*;
verus! {

pub assume_specification<T>[ <*mut T>::add ](pptr: *mut T, len: usize) -> (r: *mut T)
    requires
        pptr.addr() + len <= usize::MAX,
    ensures
        r.addr() == pptr.addr() + len * core::mem::size_of::<T>(),
;

} // verus!
