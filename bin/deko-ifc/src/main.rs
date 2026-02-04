//! Deko IFC (Information-flow Control) entry point.
//!
//! The address space shares the same with the untrusted guest kernel but the
//! memory will protected by the RMP table even if the kernel is fully aware
//! of this IFC engine, it cannot do anything harmful to the IFC engine.
//!
//! This monitor can be run at either VMPL2 or VMPL1 depends on the calling
//! context. If there is no application running, this monitor will listen to
//! system calls made by the untrusted kernel at VMPL2 and check if there is
//! any sensitive system calls; if so, this monitor will notity VMPL0 which
//! then kicks the current CPU to VMPL1. Any subsequent calls will be then
//! handled by the monitor but this now running at VMPL1.
#![no_std]
#![no_main]
#![feature(lang_items)]
#![feature(likely_unlikely)]

use deko_core::die;
use deko_core::mm::frame_allocator::DekoPageFrameAllocator;
use deko_core::mm::DEKO_IFC_FRAME_ALLOCATOR;
use deko_core::policy::DekoSyscallBody;
use deko_core::snp::is_vmpl1;
use deko_std::mem::{valid_heap_param, DekoFrameAllocator};
use deko_std::prelude::{func_ptr, PhysAddr};
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::sync::DekoSimpleOnceCell;
use deko_std::wf::WellFormed;
use deko_std::TrivialPredicate;
use vstd::prelude::*;

core::arch::global_asm!(include_str!("entry.S"), options(att_syntax));

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! { loop {} }

extern "C" {
    fn deko_heap_bottom();
    fn deko_heap_top();
}

verus! {

func_ptr!(deko_heap_bottom);

func_ptr!(deko_heap_top);

fn try_init_deko_ifc_frame_allocator() {
    if core::hint::likely(DEKO_IFC_FRAME_ALLOCATOR.get().is_some()) {
        return ;
    }
    let allocator = DekoPageFrameAllocator::new();
    let start = deko_heap_bottom_func_ptr() as usize;
    let end = deko_heap_top_func_ptr() as usize;

    if end <= start {
        die("Deko IFC heap size is zero");
    }
    assume(valid_heap_param(start as u64, (end - start) as u64, 10));

    allocator.init(start as _, (end - start) as _);

    // SAFETY: This function should only be called once during initialization.
    unsafe {
        DEKO_IFC_FRAME_ALLOCATOR.init(allocator);
    }
}

// An awkward thing is that we have no print anymore.
#[no_mangle]
#[verus_spec(r =>
        with
            Tracked(syscall_perm): Tracked<DekoPointsTo<DekoSyscallBody>>,
        requires
            syscall_perm.wf(),
            syscall_perm.is_init(),
            syscall_perm.pptr() == syscall_body@,
    )]
pub extern "C" fn deko_ifc_entry(syscall_body: DekoPPtr<DekoSyscallBody>) {
    if !is_vmpl1() {
        deko_ifc_entry_vmpl1(syscall_body);
    } else {
        die("Deko IFC at VMPL2 is not implemented yet");  // notify VMPL0
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn deko_ifc_entry_vmpl1(syscall_body: DekoPPtr<DekoSyscallBody>) {
    try_init_deko_ifc_frame_allocator();

    loop {
    }
}

} // verus!
