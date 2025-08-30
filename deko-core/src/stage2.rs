#![no_std]
#![no_main]
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
pub mod mm;
pub mod policy;
pub(crate) mod theories;

#[cfg(feature = "snp")]
pub mod snp;
#[cfg(feature = "tdx")]
pub mod tdx;

use deko_meta::{HeaderRaw, Stage2LaunchInfo};
use deko_std::prelude::*;
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use vstd::prelude::*;

use crate::cpu::idt::{create_early_idt, stage2_generic_idt_handler_no_ghcb, Idt, IdtEntry};

core::arch::global_asm!(include_str!("stage2.S"), options(att_syntax));

verus! {

#[verifier::external_body]
fn early_die() {
    unsafe {
        core::arch::asm!("ud2", options(att_syntax));
    }
}

#[verifier::external_body]
fn early_dbg() {
    unsafe {
        core::arch::asm!("hlt", options(att_syntax));
    }
}

#[verifier::external]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo<'_>) -> ! {
    crate::early_die();

    loop {}
}

/// The entry point of the stage2 in IGVM. Thanks to IGVM we do not need to
/// explicitly take care of the boot protocol and this is "automatically"
/// jumped to in `stage2.S`.
///
/// The parameters are prepared by the IGVM if configured properly.
#[verifier::exec_allows_no_decreases_clause]
#[no_mangle]
pub fn deko_main(
    s2_info: DekoPPtr<Stage2LaunchInfo>,
    Tracked(s2_info_perm): Tracked<
        &DekoPointsTo<Stage2LaunchInfo>,
    >,  // ensures read-only. todo: perhaps qualify the full path of this type?
) -> (__discard: !)
    requires
        s2_info@ === s2_info_perm.pptr(),
        s2_info_perm.is_init(),
        s2_info_perm.value().wf(),
        s2_info_perm.mem_wf(),
{

    let s2_info = s2_info.borrow(Tracked(s2_info_perm));
    let mut early_idt = Idt { entries: create_early_idt() };

    hal::setup_env(s2_info, &mut early_idt);

    loop {
    }
}

} // verus!
