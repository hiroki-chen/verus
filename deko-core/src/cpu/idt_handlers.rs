//! This module provides a set of default interrupt handlers for various CPU exceptions
//! and interrupts.
use vstd::prelude::*;

use crate::cpu::task::X86ExceptionContext;
use crate::{dbg, die, kdebug, kerror, kinfo};

verus! {

const SVM_EXIT_CPUID: usize = 0x072;

const PF_ERRNO_PRESENT: u64 = 1 << 0;

const PF_ERRNO_WRITE: u64 = 1 << 1;

const PF_ERRNO_USER: u64 = 1 << 2;

const PF_ERRNO_RSVD: u64 = 1 << 3;

const PF_ERRNO_INSTR: u64 = 1 << 4;

pub fn pretty_pf_errno(errno: u64) {
    crate::kinfo!("Page Fault Error Code: ", errno => hex);

    if errno & PF_ERRNO_PRESENT != 0 {
        crate::kinfo!("  - caused by a page-protection violation");
    } else {
        crate::kinfo!("  - caused by a non-present page");
    }

    if errno & PF_ERRNO_WRITE != 0 {
        crate::kinfo!("  - caused by a write access");
    } else {
        crate::kinfo!("  - caused by a read access");
    }

    if errno & PF_ERRNO_USER != 0 {
        crate::kinfo!("  - occurred in user mode");
    } else {
        crate::kinfo!("  - occurred in supervisor mode");
    }

    if errno & PF_ERRNO_RSVD != 0 {
        crate::kinfo!("  - caused by reserved bits being set to 1");
    }
    if errno & PF_ERRNO_INSTR != 0 {
        crate::kinfo!("  - caused by an instruction fetch");
    }
}

/// Called from VMPL1 -> VMPL1 exception handler for page faults.
#[verifier::external_body]
#[no_mangle]
#[verus_spec(
)]
unsafe extern "C" fn deko_ifc_handler_page_fault(ctx: &mut X86ExceptionContext) {
    kinfo!("Page Fault Exception occurred in VMPL1:", ctx);
    // handle this.
    // need to sanitize and forward to the guest OS for
    // the guest to handle page faults.
}

/// Called from VMPL1 -> VMPL1 exception handler for NMI.
#[verifier::external_body]
#[no_mangle]
#[verus_spec(

)]
unsafe extern "C" fn deko_ifc_handler_nmi(ctx: &mut X86ExceptionContext) {
    kinfo!("NMI occurred in VMPL1:", ctx);
    // Option 1: Forward to the guest OS NMI handler? or we just ignore it here.
    // Option 2: commit suicide.
}

#[no_mangle]
#[verus_spec(

)]
unsafe extern "C" fn ex_handler_panic(ctx: &mut X86ExceptionContext) {
    kinfo!("Panic Exception occurred:", ctx);

    die("Panic Exception");
}

#[no_mangle]
#[verus_spec(

)]
unsafe extern "C" fn ex_handler_double_fault(ctx: &mut X86ExceptionContext) {
    let rip = ctx.frame.rip;
    let rsp = ctx.frame.rsp;
    let addr = crate::cpu::regs::read_cr2();
    kerror!("Double Fault Exception occurred: rip =", rip => hex, "rsp =", rsp => hex, "CR2 =" , addr => hex);
    // No recovery possible.
    die("Double Fault Exception");
}

// We do not attempt to recover from early page faults.
// This handler is nevertheless useful as we can log the faulting
// address and error code for debugging purposes.
#[no_mangle]
unsafe extern "C" fn ex_handler_page_fault_early(ctx: &X86ExceptionContext) {
    kerror!("Early Page Fault Exception occurred during early boot.");
    let errno = ctx.error_code;
    let cr2 = crate::cpu::regs::read_cr2();
    pretty_pf_errno(errno as _);
    kerror!("faulting address (CR2):", cr2 => hex);
    die("Early Page Fault Exception");
}

#[no_mangle]
#[verifier::exec_allows_no_decreases_clause]
#[verus_spec(

)]
unsafe extern "C" fn ex_handler_page_fault(ctx: &mut X86ExceptionContext) {
    kinfo!("Page Fault Exception occurred:", ctx);

    let errno = ctx.error_code;
    let cr2 = crate::cpu::regs::read_cr2();
    pretty_pf_errno(errno as _);
    kinfo!("faulting address (CR2):", cr2 => hex);

    kinfo!("context:", ctx);

    dbg::print_stack(0);

    loop {
    }

    // stub. to be implemented.

    // Then we have to jump back to the instruction that caused the fault.
}

#[no_mangle]
unsafe extern "C" fn ex_handler_general_protection() {
    kinfo!("General Protection Fault occurred");
}

#[no_mangle]
unsafe extern "C" fn ex_handler_ve() {
    kdebug!("Virtualization Exception occurred");
}

#[no_mangle]
unsafe extern "C" fn ex_handler_syscall_handler(ctx: &mut X86ExceptionContext) {
}

/// This exception must and can only occur at VMPL1 due to some emulated instructions that
/// the guest must do.
///
/// See `vc_handle_exitcode` in `arch/x86/coco/sev/core.c`
#[no_mangle]
unsafe extern "C" fn ex_handler_vmm_handler(ctx: &mut X86ExceptionContext) {
    let errno = ctx.error_code;

    match errno {
        SVM_EXIT_CPUID => vc_handle_cpuid(ctx),
        _ => kerror!("Invalid VMM error code:", errno),
    }
}

/// Handles the `cpuid` request. We do not forward this request to the guest OS as
/// the guest OS can fake some CPUID features that might downgrade the security
/// guarantees of the whole system.
fn vc_handle_cpuid(ctx: &mut X86ExceptionContext) {
    let leaf = ctx.regs.rax as u32;
    let subfn = ctx.regs.rcx as u32;

    // TODO.

}

#[no_mangle]
unsafe extern "C" fn ex_handler_irq_ipi() {
}

#[no_mangle]
unsafe extern "C" fn ex_handler_irq_int_inj() {
}

} // verus!
