use vstd::prelude::*;

verus! {

/// A tracked enum for tracking the read/write permission on a given piece of memory.
///
/// TODO: Design privilege.
pub tracked enum PermissionDekoMem {
    Foo,
}

} // verus!
#[cfg(feature = "alloc")]
verus! {

use vstd::layout::valid_layout;
use vstd::raw_ptr::{Dealloc, DeallocData, PointsToRaw};

/// Allocate with the global allocator.
///
/// Since this relies on the global allocator we cannot directly assume anything about the
/// behavior. However, we will verify the allocator's implementation in another crate. For
/// now we just trust Rust's forwarding system.
#[verifier::external_body]
pub fn allocate(size: usize, align: usize) -> (pt: (
    *mut u8,
    Tracked<PointsToRaw>,
    Tracked<Dealloc>,
))
    requires
        valid_layout(size, align),
        size != 0,
    ensures
        pt.1@.is_range(pt.0.addr() as int, size as int),
        pt.2@@ == (DeallocData {
            addr: pt.0.addr(),
            size: size as nat,
            align: align as nat,
            provenance: pt.1@.provenance(),
        }),
        pt.0.addr() as int % align as int == 0,
        pt.0@.provenance == pt.1@.provenance(),
    opens_invariants none
{
    use core::alloc::Allocator;

    let layout = unsafe { alloc::alloc::Layout::from_size_align_unchecked(size, align) };

    let p = ::alloc::alloc::Global.allocate(layout);
    if p.is_err() {
        panic!("Failed to allocate memory");
    }
    (p.unwrap().as_ptr() as _, Tracked::assume_new(), Tracked::assume_new())
}

} // verus!
