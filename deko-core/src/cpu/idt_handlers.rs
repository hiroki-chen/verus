//! This module provides a set of default interrupt handlers for various CPU exceptions
//! and interrupts.
use vstd::prelude::*;

use crate::cpu::task::X86ExceptionContext;
use crate::{die, kdebug, kerror, kinfo};

verus! {

#[no_mangle]
#[verus_spec(

)]
unsafe extern "C" fn ex_handler_panic(ctx: &mut X86ExceptionContext) {
    let rip = ctx.frame.rip;
    let rsp = ctx.frame.rsp;
    kerror!("Panic Exception occurred: rip =", rip => hex, rsp => hex);
    die("Panic Exception");
}

#[no_mangle]
#[verus_spec(

)]
unsafe extern "C" fn ex_handler_double_fault(ctx: &mut X86ExceptionContext) {
    let rip = ctx.frame.rip;
    let rsp = ctx.frame.rsp;
    let addr = crate::cpu::regs::read_cr2();
    kerror!("Double Fault Exception occurred: rip =", rip => hex, rsp => hex, "CR2 =" , addr => hex);
    // No recovery possible.
    die("Double Fault Exception");
}

#[no_mangle]
unsafe extern "C" fn ex_handler_page_fault_early() {
}

#[no_mangle]
#[verus_spec(

)]
unsafe extern "C" fn ex_handler_page_fault(ctx: &mut X86ExceptionContext) {
    let errno = ctx.error_code;
    let cr2 = crate::cpu::regs::read_cr2();
    kinfo!("page fault error code:", errno => hex);
    kinfo!("faulting address (CR2):", cr2 => hex);

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
