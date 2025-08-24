#![no_std]
#![no_main]
#![feature(never_type)]

use core::option;

use deko_core::cpu::idt::{create_early_idt, stage2_generic_idt_handler_no_ghcb, Idt, IdtEntry};
use deko_core::hal;
use deko_core::hal::PlatformType;
use deko_meta::HeaderRaw;
use deko_std::prelude::*;
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use vstd::prelude::*;

core::arch::global_asm!(include_str!("stage2.S"), options(att_syntax));

verus! {

#[verifier::external]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}

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
#[verifier::external_body]
#[no_mangle]
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
    // For SNP, the logging is enabled via GHCB.
    // #[cfg(feature = "tdx")]
    // deko_core::logging::init_logger();

    let header = header.borrow(Tracked(&header_content));
    let platform_type = PlatformType::from(header.platform_type);

    let mut early_idt = Idt { entries: create_early_idt() };
    hal::init_platform(platform_type, &mut early_idt, header);

    // Initialize the CPUID table to detect CPU cores.

    loop {
    }
}

} // verus!
