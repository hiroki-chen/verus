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

} // verus!
