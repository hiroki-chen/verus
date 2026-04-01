#![no_std]
#![no_main]
#![feature(alloc_error_handler)]
#![allow(improper_ctypes_definitions)]
#![feature(proc_macro_hygiene)]

use deko_core::cpu::ctx::{DekoCtx, DekoCtxPermission};
use deko_core::hal::set_is_stage2;
use deko_std::prelude::*;
use vstd::prelude::*;

core::arch::global_asm!(include_str!("../stage2.S"), options(att_syntax));

#[alloc_error_handler]
fn alloc_error(_layout: core::alloc::Layout) -> ! { early_die(); }

verus! {

#[allow(unreachable_code)]
#[verifier::external]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo<'_>) -> ! {
    // Print detailed panic information using the logging system
    #[cfg(feature = "logging")]
    deko_core::logging::print_panic_info(info);

    // Note that there is no stack unwinding
    // so the information might be incorrect.

    early_die();

    loop {
    }
}

/// The entry point for the stage2 kernel for BSP.
///
/// The parameter `ctx` is obtained from the assembly code where we pass the address
/// from the `.data` section to here.
#[no_mangle]
#[verifier::external_body]
#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<DekoCtxPermission>,
    requires
        ctx_perm.wf_with(ctx),
        ctx_perm.current_cpu_core.is_bsp(),
        ctx_perm.pgtable_perm.mapped_region(VirtAddr(0)..VirtAddr(LOWMEM_END as u64)),
)]
extern "C" fn deko_main(ctx: DekoPPtr<DekoCtx>) -> (__discard: !) {
    set_is_stage2(true);
    // Verus does not generate correct symbol for this
    // so now we mark it as external body.
    deko_core::hal::setup_env(ctx);
}

} // verus!
