//! This module provides a set of default interrupt handlers for various CPU exceptions
//! and interrupts.
use deko_std::sync::DekoAtomicData;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::cpu::task::X86ExceptionContext;
use crate::cpu::{CPUID_MAX_COUNT, CPUID_TABLE};
use crate::{dbg, die, kdebug, kerror, kinfo, kpanic_if, ktrace};

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
    let errno = ctx.error_code;
    let cr2 = crate::cpu::regs::read_cr2();
    pretty_pf_errno(errno as _);
    kinfo!("faulting address (CR2):", cr2 => hex);

    kinfo!("context:", ctx);

    dbg::print_stack(0);

    loop {
    }
}

#[no_mangle]
unsafe extern "C" fn ex_handler_general_protection(ctx: &mut X86ExceptionContext) {
    kinfo!("General Protection Fault occurred:", ctx);
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

    ktrace!("VMM Exception occurred in VMPL1:", ctx);

    match errno {
        SVM_EXIT_CPUID => vc_handle_cpuid(ctx),
        _ => kerror!("Invalid VMM error code:", errno),
    }
}

#[inline]
fn cpuid_requires_ecx(leaf: u32) -> bool {
    match leaf {
        0x4
        | 0x7
        | 0xB
        | 0xD
        | 0xF
        | 0x10
        | 0x12
        | 0x14
        | 0x17
        | 0x18
        | 0x1D
        | 0x1E
        | 0x1F
        | 0x8000001D
        | 0x80000020
        | 0x80000026 => true,
        _ => false,
    }
}

/// Handles the `cpuid` request. We do not forward this request to the guest OS as
/// the guest OS can fake some CPUID features that might downgrade the security
/// guarantees of the whole system.
#[verus_spec()]
fn vc_handle_cpuid(ctx: &mut X86ExceptionContext) {
    let leaf = ctx.regs.rax as u32;
    let subfn = ctx.regs.rcx as u32;

    ktrace!("Received CPUID request: leaf =", leaf => hex, "subfn =", subfn => hex);

    if let Some(DekoAtomicData { data: cpu_id, .. }) = CPUID_TABLE.get() {
        let mut i = 0;
        let mut found = false;
        let check_ecx = cpuid_requires_ecx(leaf);

        #[verus_spec(
            invariant
                i <= cpu_id.func@.len(),
                cpu_id.wf(),
            decreases
                cpu_id.func@.len() - i,
        )]
        while i < cpu_id.func.len() {
            let fns = cpu_id.func.index(i);
            let ecx_matches = if check_ecx {
                fns.ecx_in == subfn
            } else {
                true
            };

            if fns.eax_in == leaf && ecx_matches {
                ctx.regs.rax = fns.eax_out as u64;
                ctx.regs.rbx = fns.ebx_out as u64;
                ctx.regs.rcx = fns.ecx_out as u64;
                ctx.regs.rdx = fns.edx_out as u64;

                found = true;

                ktrace!("Handled CPUID request: leaf =", leaf => hex, "subfn =", subfn => hex, "output: rax =", ctx.regs.rax => hex, "rbx =", ctx.regs.rbx => hex, "rcx =", ctx.regs.rcx => hex, "rdx =", ctx.regs.rdx => hex);

                break ;
            }
            i += 1;
        }

        if !found {
            ctx.regs.rax = 0;
            ctx.regs.rbx = 0;
            ctx.regs.rcx = 0;
            ctx.regs.rdx = 0;
        }
    } else {
        kerror!("CPUID table not initialized");
    }

    // Advance the RIP to skip the `cpuid` instruction. The `cpuid` instruction is 2 bytes long.
    ctx.frame.rip = ctx.frame.rip.wrapping_add(2);  // skip the `cpuid` instruction
}

#[no_mangle]
extern "C" fn debug_iret_frame(rdi: u64, cs: u64, rflags: u64, rsp: u64, ss: u64) {
    kdebug!("Debug IRET frame: rdi =", rdi => hex, "cs =", cs => hex, "rflags =", rflags => hex, "rsp =", rsp => hex, "ss =", ss => hex);
}

#[no_mangle]
unsafe extern "C" fn ex_handler_irq_ipi() {
}

#[no_mangle]
unsafe extern "C" fn ex_handler_irq_int_inj() {
}

} // verus!
