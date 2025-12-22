//! This module provides a set of default interrupt handlers for various CPU exceptions
//! and interrupts.
use vstd::prelude::*;

verus! {

#[no_mangle]
unsafe extern "C" fn ex_handler_panic() {
}

#[no_mangle]
unsafe extern "C" fn ex_handler_double_fault() {
}

#[no_mangle]
unsafe extern "C" fn ex_handler_page_fault_early() {
}

#[no_mangle]
unsafe extern "C" fn ex_handler_page_fault() {
}

#[no_mangle]
unsafe extern "C" fn ex_handler_general_protection() {
}

#[no_mangle]
unsafe extern "C" fn ex_handler_ve() {
}

#[no_mangle]
unsafe extern "C" fn ex_handler_syscall_handler() {
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
