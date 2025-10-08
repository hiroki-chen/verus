#![no_std]
#![no_main]
#![feature(abi_x86_interrupt)]
#![feature(allocator_api)]
#![feature(never_type)]
#![allow(named_asm_labels)]
#![allow(binary_asm_labels)]

#[cfg(not(target_arch = "x86_64"))]
compile_error!("Cannot be compiled against non x86_64 architecture!");

#[cfg(all(feature = "tdx", feature = "snp"))]
compile_error!("Cannot enable both TDX and SEV features at the same time!");

pub mod allocator;
pub mod boot;
pub mod cpu;
pub mod hal;
pub mod logging;
pub mod mm;
pub mod policy;
pub(crate) mod theories;

#[cfg(feature = "snp")]
pub mod snp;
#[cfg(feature = "tdx")]
pub mod tdx;

use deko_std::prelude::*;
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use vstd::prelude::*;

use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};

core::arch::global_asm!(include_str!("stage2.S"), options(att_syntax));

verus! {

#[verifier::external]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo<'_>) -> ! {
    crate::early_die();

    loop {
    }
}

/// The entry point for the stage2 kernel for BSP.
///
/// The parameter `ctx` is obtained from the assembly code where we pass the address
/// from the `.data` section to here.
#[no_mangle]
pub fn deko_main(ctx: DekoPPtr<DekoCtx>, ctx_perm: Tracked<DekoCtxPermission>) -> (__discard: !)
    requires
        ctx_perm@.wf_with(ctx),
        ctx_perm@.current_cpu_core.is_bsp(),
{
    // let s2_info = s2_info.borrow(Tracked(s2_info_perm));
    // let mut early_idt = Idt { entries: create_early_idt() };
    hal::setup_env(ctx, ctx_perm);
}

} // verus!
