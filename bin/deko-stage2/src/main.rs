#![no_std]
#![no_main]

use vstd::prelude::*;

use deko_std::prelude::*;
use deko_core::cpu::ctx::{DekoCtx, DekoCtxPermission};

core::arch::global_asm!(include_str!("../stage2.S"), options(att_syntax));

verus! {

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
#[unsafe(no_mangle)]
// Making this function as `external` is awkward as
// verus treats imports from `deko_core` as external.
#[verifier::external]
#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<DekoCtxPermission>,
    requires
        ctx_perm.wf_with(ctx),
        ctx_perm.current_cpu_core.is_bsp(),
)]
extern "C" fn deko_main(ctx: DekoPPtr<DekoCtx>) -> (__discard: !) {
    deko_core::hal::setup_env(ctx);
}

} // verus!
