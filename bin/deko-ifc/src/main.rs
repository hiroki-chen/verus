#![no_std]
#![no_main]
#![feature(lang_items)]

use deko_core::policy::DekoSyscallBody;
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

core::arch::global_asm!(include_str!("entry.S"), options(att_syntax));

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! { loop {} }

verus! {

// An awkward thing is that we have no print anymore.
#[no_mangle]
#[link_section = ".text.entry"]
#[verifier::exec_allows_no_decreases_clause]
#[verus_spec(r =>
        with
            Tracked(syscall_perm): Tracked<DekoPointsTo<DekoSyscallBody>>,
        requires
            syscall_perm.wf(),
            syscall_perm.is_init(),
            syscall_perm.pptr() == syscall_body@,
    )]
pub extern "C" fn deko_ifc_entry(syscall_body: DekoPPtr<DekoSyscallBody>) -> ! {
    loop {
    }
}

} // verus!
