use vstd::prelude::*;

pub(crate) mod imp;

verus! {

/// A simple allocator.
pub struct Allocator {}

pub ghost struct AllocatorSpec {}

} // verus!
verus! {

impl Allocator {
    pub const fn new() -> Self {
        Allocator {  }
    }
}

} // verus!
