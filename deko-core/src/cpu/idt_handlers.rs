//! This module provides a set of default interrupt handlers for various CPU exceptions
//! and interrupts.
use vstd::prelude::*;

use crate::cpu::task::X86ExceptionContext;
use crate::{dbg, die, kdebug, kerror, kinfo};

verus! {

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

#[verifier::external_body]
#[no_mangle]
#[verus_spec(

)]
unsafe extern "C" fn ex_handler_panic(ctx: &mut X86ExceptionContext) {
    kinfo!("Panic Exception occurred:", ctx);

    let doorbell = core::slice::from_raw_parts(ctx.regs.rdi as *const u8, 0x100);

    kinfo!("  ", doorbell);

    let (cpu, Tracked(perm)) = crate::cpu::DekoCpuCtx::this_cpu();
    let cpu = cpu.borrow(Tracked(&perm.ptr_perm));

    let irq_was_enabled = cpu.nested_irq.state.load(Tracked(&perm.irq_state_perm.state_perm));
    kinfo!("  - CPU IRQ enabled state before exception:", irq_was_enabled);
    let count = cpu.nested_irq.counts[0].load(Tracked::assume_new());
    kinfo!("  - CPU nested IRQ count level 0 before exception:", count);

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
}

#[no_mangle]
unsafe extern "C" fn ex_handler_ve() {
}

#[no_mangle]
unsafe extern "C" fn ex_handler_syscall_handler(ctx: &mut X86ExceptionContext) {
}

#[no_mangle]
unsafe extern "C" fn ex_handler_vmm_handler() {
}

#[no_mangle]
unsafe extern "C" fn ex_handler_irq_ipi() {
}

#[no_mangle]
unsafe extern "C" fn ex_handler_irq_int_inj() {
}

} // verus!
