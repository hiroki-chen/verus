use vstd::prelude::*;

pub(crate) mod imp;

/// Definitions
verus! {

/// A simple allocator.
pub struct Allocator {}

pub ghost struct AllocatorSpec {}

} // verus!

/// Implementations
verus! {

impl Allocator {
    pub const fn new() -> Self {
        Allocator {  }
    }
}

} // verus!
