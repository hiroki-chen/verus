use vstd::prelude::*;

use crate::slice::slice_wf;
use crate::WellFormed;

verus! {

impl<T: WellFormed, A: core::alloc::Allocator> WellFormed for alloc::vec::Vec<T, A> {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        slice_wf(self@)
    }
}

pub assume_specification<T, A>[ alloc::vec::Vec::<T, A>::as_ptr ](v: &alloc::vec::Vec<T, A>) -> (r:
    *const T) where A: core::alloc::Allocator
    ensures
        r.addr() + v@.len() * core::mem::size_of::<T>() <= usize::MAX,
;

pub assume_specification<T, A>[ alloc::vec::Vec::<T, A>::as_mut_ptr ](
    v: &mut alloc::vec::Vec<T, A>,
) -> (r: *mut T) where A: core::alloc::Allocator
    ensures
        v@ =~= old(v)@,
        r.addr() + v@.len() * core::mem::size_of::<T>() <= usize::MAX,
;

} // verus!
