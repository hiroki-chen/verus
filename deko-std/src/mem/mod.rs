//! This crate implements the memory management for the Deko monitor.
//!
//! We illustrate the memory hierarchy as follows:
//!
//!```text
//!  ┌──────────────────────────────────┐
//!  │                                  │
//!  │                                  │
//!  │             L2 VMs               │
//!  │                                  │
//!  │                                  │
//!  └───────┬───────────────────┬──────┘
//!          │                   │
//!          │                   │
//!  ┌───────▼──────┐    ┌───────▼──────┐
//!  │              │    │              │
//!  │   Deko Mem   │    │   Deko Mem   │
//!  │              │    │              │
//!  ├──────────────┤    ├──────────────┤
//!  │              │    │              │
//!  │      MM      │    │      MM      │
//!  │              │    │              │
//!  └──────┬───────┘    └───────┬──────┘
//!         │                    │
//!         │                    │
//!         │                    │
//!         │                    │
//!  ┌──────▼────────────────────▼───────┐
//!  │                                   │
//!  │                                   │
//!  │           DekoAllocator           │
//!  │                                   │
//!  │                                   │
//!  └───────────────────────────────────┘
//!  ┌───────────────────────────────────┐
//!  │                                   │
//!  │                                   │
//!  │               Heap                │
//!  │                                   │
//!  │                                   │
//!  └───────────────────────────────────┘
//!```
//!
//! Note that in the L2 VM's points of view, the Deko Mem is the only memory
//! region that it can access and starts at 0x0.
//!
//!
//! The buddy allocation algorithm is heavily referenced from:
//!     https://github.com/DrChat/buddyalloc.git
//!
//! We thank the author(s) for their work and the license is MIT.
#[cfg(feature = "alloc")]
pub mod allocator;
pub mod heap;
pub mod perm;

#[cfg(feature = "alloc")]
pub use allocator::*;
pub use heap::*;
pub use perm::*;
use vstd::prelude::*;

verus! {

struct Allocator;

#[verifier::external]
unsafe impl core::alloc::GlobalAlloc for Allocator {
    unsafe fn alloc(&self, _layout: core::alloc::Layout) -> *mut u8 {
        panic!("DekoHeapAllocator is not used as the global allocator by default. Use DekoHeapAllocator::alloc instead.");
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: core::alloc::Layout) {
        panic!("DekoHeapAllocator is not used as the global allocator by default. Use DekoHeapAllocator::dealloc instead.");
    }
}

/// We do not use Rust's global allocator by default so this is just a dummy one.
/// Any use of the global allocator will panic.
#[verifier::external]
#[global_allocator]
static __DISCARD: Allocator = Allocator;

} // verus!
