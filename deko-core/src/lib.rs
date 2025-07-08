//! ┌────────────────────────────────────────┐
//! │ ┌────────────────────────────────────┐ │
//! │ │                                    │ │
//! │ │                                    │ │
//! │ │            Linux Kernel            │ │
//! │ │                                    │ │
//! │ └────────────────────────────────────┘ │
//! │ ┌────────────────────────────────────┐ │
//! │ │                                    │ │
//! │ │                                    │ │
//! │ │            Deko Monitor            │ │
//! │ │                                    │ │
//! │ └────────────────────────────────────┘ │
//! │                                        │
//! │                               TDX  CVM │
//! └────────────────────────────────────────┘
//! ┌────────────────────────────────────────┐
//! │                                        │
//! │               Hypervisor               │
//! │                                        │
//! └────────────────────────────────────────┘
//!
//! We implement the deko monitor as an L1 guest in the TDX architecture based on the
//! TD partition model.
#![no_std]
#![feature(abi_x86_interrupt)]

#[cfg(target_arch = "x86")]
compile_error!("Cannot be compiled against non x86_64 architecture!");

extern crate alloc;

pub mod allocator;
pub mod boot;
pub mod cell;
pub mod cpu;
pub mod policy;
pub mod sync;

#[cfg(feature = "tdx")]
pub mod tdx;

use alloc::alloc::GlobalAlloc;

use deko_meta::Header;
use tdx::tdcall::check_tdcall;
use vstd::prelude::*;

/// A global allocator for the monitor.
#[verifier::external]
#[global_allocator]
pub static ALLOC: crate::allocator::Allocator = crate::allocator::Allocator::new();

verus! {

/// The entry point of our monitor (BSP will enter this first).
///
/// This function is called by the bootstrap code after the monitor is loaded into
/// memory and the context is prepared and does the following stuff:
///
/// 1. Initialize the global allocator (a.k.a. the memory).
/// 2. Initialize logging (optional) if needed.
/// 3. Initialize the page table.
/// 4. Initialize the memory management subsystem.
/// 5. Initialize the interrupt.
/// 6. Initialize the CPU subsystem.
/// 7. Initialize the ACPI table.
/// 8. Prepare for loading the Linux kernel which is packaed as the final payload.
#[verifier::exec_allows_no_decreases_clause]
#[verifier::external_body]
pub fn deko_main(header: &'static Header) -> ! {
    if !check_tdcall() {
        unsafe {
            core::arch::asm!("ud2", options(nomem, nostack, preserves_flags));
        }
    }
    // Initialize the global allocator.
    // This is crucial as we now are still under UEFI mm which means
    // vaddr == paddr.
    // cpu_idle();

    loop {
    }
}

/// The entry function of other application processors for SMP systems.
#[no_mangle]
#[verifier::external_body]
pub unsafe extern "C" fn _ap_start() -> ! {
    loop {
    }
}

} // verus!
