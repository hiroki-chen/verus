//! Deko IFC (Information-flow Control) entry point.
//!
//! The code here must run at the VMPL1 privilege level inside the guest VM.
//! Typicallt this code is invoked by the `syscall` after overwriting the
//! LSTAR register in the VMPL1's VMSA.
//!
//! The address space shares the same with the untrusted guest kernel but the
//! memory will protected by the RMP table even if the kernel is fully aware
//! of this IFC engine, it cannot do anything harmful to the IFC engine.
#![no_std]
#![no_main]
#![feature(lang_items)]

use deko_core::mm::frame_allocator::DekoPageFrameAllocator;
use deko_core::policy::DekoSyscallBody;
use deko_std::mem::DekoFrameAllocator;
use deko_std::prelude::func_ptr;
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::wf::WellFormed;
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

// pub exec static DEKO_IFC_FRAME_ALLOCATOR: DekoPageFrameAllocator<10> = DekoPageFrameAllocator::new(); should be an once /lazy cell.
fn try_init_deko_ifc_frame_allocator() {
    // if core::hint::likely(DEKO_IFC_FRAME_ALLOCATOR.get().is_some()) {
    //     return;
    // }
    // SAFETY: This function should only be called once during initialization.
    // unsafe {
    //     DEKO_IFC_FRAME_ALLOCATOR.init(
    //         deko_heap_bottom() as usize,
    //         deko_heap_top() as usize,
    //     );
    // }
}

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
    try_init_deko_ifc_frame_allocator();

    loop {
    }
}

} // verus!
