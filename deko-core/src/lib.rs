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
//! │                                    CVM │
//! └────────────────────────────────────────┘
//! ┌────────────────────────────────────────┐
//! │                                        │
//! │               Hypervisor               │
//! │                                        │
//! └────────────────────────────────────────┘
#![no_std]
#![feature(abi_x86_interrupt)]

#[cfg(target_arch = "x86")]
compile_error!("Cannot be compiled against non x86_64 architecture!");

#[cfg(all(feature = "tdx", feature = "snp"))]
compile_error!("Cannot enable both TDX and SEV features at the same time!");

extern crate alloc;

pub mod allocator;
pub mod boot;
pub mod cell;
pub mod cpu;
pub mod hal;
pub mod policy;
pub mod sync;

#[cfg(feature = "snp")]
pub mod snp;
#[cfg(feature = "tdx")]
pub mod tdx;

use alloc::alloc::GlobalAlloc;

use deko_meta::Header;
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
    unsafe {
        // core::arch::asm!("ud2");
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
