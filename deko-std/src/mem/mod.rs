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
pub mod bitalloc;
pub mod heap;
pub mod paging;
pub mod perm;

#[cfg(feature = "alloc")]
pub use allocator::*;
pub use heap::*;
pub use paging::*;
pub use perm::*;
use vstd::prelude::*;

use crate::FixedAddressMappingRange;

verus! {

pub uninterp spec fn cr3_value() -> u64;

/// Gets the initial page table's value for system initialization.
///
/// This uninterpreted function represents the physical address of the initial
/// page table set up during boot. The actual value is platform-specific.
pub uninterp spec fn initial_page_table_value() -> u64;

/// Indicates the valid range of PTE physical addresses that can be used in the system.
///
/// Returns (start, end) where start <= valid_paddr < end for any valid PTE.
pub uninterp spec fn valid_pte_phys_range() -> (u64, u64);

/// Indicates the valid range of virtual addresses that can be used in the system.
///
/// Returns (start, end) where start <= valid_vaddr < end for any valid virtual address.
pub uninterp spec fn valid_pte_virt_range() -> (u64, u64);

/// Indicates the valid range of kernel mapping.
///
/// Defines the fixed address mapping range used for kernel memory regions.
pub uninterp spec fn valid_kernel_mapping_range() -> FixedAddressMappingRange;

/// Indicates the valid range of the heap mapping area.
///
/// Defines the fixed address mapping range used for heap memory allocation.
pub uninterp spec fn valid_heap_mapping_range() -> FixedAddressMappingRange;

} // verus!
