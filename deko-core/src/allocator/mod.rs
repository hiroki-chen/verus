use alloc::alloc::{Allocator, GlobalAlloc, Layout};

use deko_std::sync::{Arc, Mutex};
use deko_std::wf::WellFormed;
use vstd::prelude::*;
use vstd::view::View;

pub(crate) mod imp;

verus! {

/// A trait that defines the interface for a Deko allocator.
///
/// We do not use the Rust's default [`alloc::alloc::Allocator`] APIs mainly due to
/// inconsistencies between high-level Verus verified objects and Rust-wrapped for-
/// eign types such as [`core::ptr::NonNull`] and [`core::result::Result`] which
/// prevent us from defining a unified and clean verification interface.
pub trait DekoAlloc: WellFormed {

}

/// The system-wide allocator for the Deko monitor, and this is just a think
/// wrapper around a specific allocator implementation that implements the
/// [`DekoAlloc`] trait.
pub struct DekoAllocator<A: DekoAlloc>(A);

impl<A: DekoAlloc> View for DekoAllocator<A> {
    type V = A;

    closed spec fn view(&self) -> Self::V {
        self.0
    }
}

impl<A: DekoAlloc> DekoAllocator<A> {
    pub const fn new(alloc: A) -> (s: Self)
        requires
            alloc.wf(),
        ensures
            s@.wf(),
    {
        Self(alloc)
    }
}

#[verifier::external]
unsafe impl<A: DekoAlloc> GlobalAlloc for DekoAllocator<A> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        todo!()
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        todo!()
    }
}

} // verus!
