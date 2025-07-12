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
#![feature(never_type)]

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
pub mod logging;
pub mod policy;
pub mod sync;
pub(crate) mod theories;

#[cfg(feature = "snp")]
pub mod snp;
#[cfg(feature = "tdx")]
pub mod tdx;

use deko_meta::HeaderRaw;
use deko_std::sync::*;
use vstd::prelude::*;
use vstd::simple_pptr::{PPtr, PointsTo};

use crate::hal::PlatformType;

verus! {

/// A global platform type that is initialized at the beginning of the program.
///
/// # Note
///
/// This is due to a bug in verus as it panics on cross-module static variable
/// references so we have to pin every static variable to the current module.
pub exec static PLATFORM: OnceLock<PlatformType>
    ensures
        PLATFORM.wf(),
{
    OnceLock::new()
}

/// A global allocator for the monitor.
#[verifier::external]
#[global_allocator]
pub exec static ALLOC: crate::allocator::Allocator = crate::allocator::Allocator::new();

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
#[verifier::exec_allows_no_decreases_clause]
pub fn deko_main(
    header: PPtr<HeaderRaw>,
    Tracked(header_content): Tracked<
        &PointsTo<HeaderRaw>,
    >,  // ensures read-only. todo: perhaps qualify the full path of this type?
) -> (__discard: !)
    requires
        header_content.is_init(),
        header === header_content.pptr(),
// nothing to be ensured here.

{
    // TODO: The platform should be initialized like this:
    // let platform_type = SvsmPlatformType::from(launch_info.platform_type);
    crate::logging::init_logger();

    PLATFORM.init(PlatformType::Snp);

    // let aaa = PLATFORM.get();

    // Log the initialization message.
    // crate::logging::log(log::Level::Info, format_args!("Deko Monitor initialized!"));

    // Initialize the global allocator.
    // This is crucial as we now are still under UEFI mm which means
    // vaddr == paddr.
    // cpu_idle();
    loop {
    }
}

// The entry function of other application processors for SMP systems.
// #[unsafe(no_mangle)]
// #[verifier::external_body]
// pub unsafe extern "C" fn _ap_start() -> ! {
//     loop {
//     }
// }
} // verus!
