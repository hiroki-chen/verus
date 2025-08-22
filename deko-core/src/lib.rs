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
#![feature(allocator_api)]
#![feature(never_type)]

#[cfg(not(target_arch = "x86_64"))]
compile_error!("Cannot be compiled against non x86_64 architecture!");

#[cfg(all(feature = "tdx", feature = "snp"))]
compile_error!("Cannot enable both TDX and SEV features at the same time!");

pub mod address;
pub mod allocator;
pub mod boot;
pub mod cpu;
pub mod hal;
pub mod logging;
pub mod policy;
pub(crate) mod theories;

#[cfg(feature = "snp")]
pub mod snp;
#[cfg(feature = "tdx")]
pub mod tdx;

use deko_meta::HeaderRaw;
use deko_std::prelude::*;
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use vstd::prelude::*;

use crate::cpu::idt::{create_early_idt, stage2_generic_idt_handler_no_ghcb, Idt, IdtEntry};
use crate::hal::PlatformType;

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
///
/// # Arguments
///
/// - `header`: A permissioned pointer to the header of the monitor, which contains metadata about the monitor.
/// - `header_permission`: A tracked struct for determining the access permission of our header (read-only).
///
/// # References
///
/// https://github.com/coconut-svsm/svsm/blob/main/kernel/src/stage2.rs
#[verifier::exec_allows_no_decreases_clause]
pub fn deko_main(
    header: DekoPPtr<HeaderRaw>,
    Tracked(header_content): Tracked<
        &DekoPointsTo<HeaderRaw>,
    >,  // ensures read-only. todo: perhaps qualify the full path of this type?
) -> (__discard: !)
    requires
        header_content.is_init(),
        header@ === header_content.pptr(),
        header_content.value().wf(),
        header_content.mem_wf(),
    ensures
        false,
{
    // crate::logging::init_logger();

    let platform_type = header.borrow(Tracked(&header_content));
    let platform_type = PlatformType::from(platform_type.platform_type);

    let mut early_idt = Idt { entries: create_early_idt() };
    crate::cpu::idt::init_early_idt(&mut early_idt);

    hal::init_platform(platform_type);

    // Initialize the CPUID table to detect CPU cores.

    loop {
    }
}

} // verus!
