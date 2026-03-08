use deko_std::cpu::write_msr;
use deko_std::mem::{valid_heap_param, DekoFrameAllocator};
use deko_std::misc::early_die;
use deko_std::prelude::{func_ptr, PhysAddr};
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::sync::DekoSimpleOnceCell;
use deko_std::wf::WellFormed;
use deko_std::TrivialPredicate;
use vstd::prelude::*;

use crate::cpu::irq::{irq_enable, irq_enabled, log_nested_irq_state, raw_irq_enable};
use crate::cpu::DekoCpuCtx;
use crate::guest::{request_vmpl2_syscall_handler, DekoGuestServResult};
use crate::mm::frame_allocator::DekoPageFrameAllocator;
use crate::mm::DEKO_IFC_FRAME_ALLOCATOR;
use crate::policy::syscall::{analyze_and_prepare_syscall, sysret_epilogue};
use crate::policy::{syscall, DekoSyscallBody};
use crate::snp::ghcb::{current_ghcb, GuestHostCommunicationBlock};
use crate::snp::{doorbell, is_vmpl1, is_vmpl1_user, MSR_AMD64_SEV_ES_GHCB};
use crate::{die, kerror, kinfo};

verus! {

#[verifier::external_body]
fn replace_stack(syscall_body: DekoPPtr<DekoSyscallBody>) -> u64 {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let vmpl1_stack = cpu_borrow.ext_vmpl1.as_ref().unwrap().vmpl1_stack;
    let ret: u64;

    unsafe {
        core::arch::asm!(
            "
                pushq %r12
                movq %rsp, %r12
                movq {0}, %rsp
                callq *{1}
                movq %r12, %rsp
                popq %r12
            ",
            in(reg) vmpl1_stack.0,
            in(reg) deko_ifc_entry_vmpl1 as usize,
            in("rdi") syscall_body.into_vaddr().0,
            out("rax") ret,
            clobber_abi("C"),
            options(att_syntax)
        );
    }

    ret
}

// Need to switch to a large stack here.
#[allow(improper_ctypes_definitions)]
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
    if is_vmpl1_user() {
        // Swap the current stack to the per-CPU large stack.
        replace_stack(syscall_body);
    } else {
        die("Deko IFC at VMPL2 is not implemented yet");  // notify VMPL0
    }
}

#[verifier::exec_allows_no_decreases_clause]
#[verus_spec(
    with
        Tracked(syscall_perm): Tracked<DekoPointsTo<DekoSyscallBody>>,
    requires
        syscall_perm.wf(),
        syscall_perm.is_init(),
        syscall_perm.pptr() == syscall_body_ptr@,
)]
fn deko_ifc_entry_vmpl1(syscall_body_ptr: DekoPPtr<DekoSyscallBody>) -> u64 {
    // From now, this is the bottom half of the system call handler, and
    // we are safe to re-enable interrupts and call other functions.
    //
    // Thus we enable IRQs and check if if there is nested IRQs and
    // now we keep it in sync with the per-CPU IRQ state in `DekoCpuCtx`.
    raw_irq_enable();
    crate::imp::after_irq_enable();

    let tracked mut syscall_perm = syscall_perm;
    let mut syscall_body = syscall_body_ptr.take(Tracked(&mut syscall_perm));

    // First analyze the syscall.
    if let Err(e) = analyze_and_prepare_syscall(&mut syscall_body) {
        return e.into_result_code();
    }
    // Then request VMPL2 to handle the syscall.

    kinfo!("ifc: before request_vmpl2_syscall_handler");

    if let Err(e) = request_vmpl2_syscall_handler() {
        kerror!("ifc: request_vmpl2_syscall_handler failed");
        return e.into_result_code();
    }
    kinfo!("ifc: after request_vmpl2_syscall_handler");
    // Check the syscall return value and prepare for returning to the guest.
    kinfo!("ifc: before sysret_epilogue");

    if let Err(e) = sysret_epilogue(&mut syscall_body) {
        kerror!("ifc: sysret_epilogue failed");
        return e.into_result_code();
    }
    kinfo!("ifc: after sysret_epilogue");
    syscall_body_ptr.write(Tracked(&mut syscall_perm), syscall_body);

    0
}

func_ptr!(deko_ifc_entry);

} // verus!
