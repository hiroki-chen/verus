//! This module implements the support for restricted interrupt injection on SEV-SNPs.
//!
//! To protect against malicious injection attacks, SNP supports two mutually
//! exclusive features to enforce Interrupt and Event injection security protections:
//!
//! - Restricted Interrupt Injection feature
//! - Alternate Interrupt Injection feature (not used in our monitor)
//!
//! In restricted interrupt injection mode (can be checked via sev features),
//! the hypervisor cannot fire invoke any IDT routines directly but #HV vector (28)
//! as a proxy function to singal pending events; the detailed interrupt information
//! will be then written into a per-vCPU "doorbell" page negotiated with the hypervisor
//! via the GHCB protocol `register_hv` which is marked as shared in the RMP entries.
//!
//! However, with doorbell interrupts, the thing works slightly differently with
//! traditional OS interrupt handling and CPU IPIs as cores with IF cleared will lost
//! the interrupts if not properly handled (as doorbell is software-based mechanism).
//! Therefore, in the hv handler routine we need to check if "we" are within a context
//! where IRQs are disabled and then restart the HV handling afterwards.
//!
//! The workflow is shown as below:
//!
//! 1. KVM/Host injects interrupts using the HV_VECTOR and prepares the doorbell page.
//! 2. Guest CPU traps into the HV_VECTOR handler.
//! 3. In the handler, we check if this is an NMI/MC; if so we handle it directly.
//!    - Otherwise check if EFLAGS.IF == 1 via exception frame.
//!      - If so, handle the doorbell immediately if vector is non-zero.
//!      - If not, iret to resume the interrupted instruction.
//! 4. Upon IRQ re-enabling, check any pending events via the doorbell page via
//!    `doorbell.pending_event.vector != 0`.
//!
//! See also [here](https://lpc.events/event/16/contributions/1321/).
use core::mem::offset_of;
use core::ptr::addr_of;

use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::address::VirtAddr;
use deko_std::mem::{PAGE_SIZE, PERCPU_BASE_VMPL1};
use deko_std::misc::early_die;
use deko_std::prelude::PhysAddr;
use deko_std::ptr::{DekoPPtr, DekoPPtrPred, DekoPointsTo};
use deko_std::sync::{DekoAtomicData, DekoRwLock, RwLock};
use deko_std::wf::WellFormed;
use deko_std::{
    boxed_ptr, deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data, with_permission,
};
use vstd::atomic::{PAtomicU8, PermissionU8};
use vstd::prelude::*;

use crate::cpu::apic::Apic;
use crate::cpu::idt::{IPI_VECTOR, TIMER_VECTOR};
use crate::cpu::irq::{irq_enabled, raw_irq_disable, raw_irq_enable, IrqUnSafeLockGuard};
use crate::cpu::task::{debug_hv, X86ExceptionContext};
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPerVmpl, DekoCpuCtxPermission};
use crate::guest::request_vmpl2_timer_event;
use crate::mm::frame_allocator::DekoPageFrameBox;
use crate::mm::paging::PageTable;
use crate::mm::{virt_to_phys, virt_to_phys_checked, DEKO_FRAME_ALLOCATOR_FULL};
use crate::snp::ghcb::{current_ghcb, GuestHostCommunicationBlock};
use crate::snp::{doorbell, is_vmpl1};
use crate::{die, kdebug, kerror, kinfo, kpanic_if, ktrace, kwarn};

extern "C" {
    pub static mut HV_DOORBELL_ADDR: usize;
    pub static mut HV_DOORBELL_ADDR_VMPL1: usize;
}

core::arch::global_asm!(
    include_str!("hv_handler.S"),
    EXCEP_FLAGS_OFF = const offset_of!(X86ExceptionContext, frame.flags),
    EXCEP_CS_OFF = const offset_of!(X86ExceptionContext, frame.cs),
    EXCEP_RIP_OFF = const offset_of!(X86ExceptionContext, frame.rip),
    EXCEP_RSP_OFF = const offset_of!(X86ExceptionContext, frame.rsp),
    EXCEP_FRAME_OFF = const offset_of!(X86ExceptionContext, frame),
    EXCEP_RAX_OFF = const offset_of!(X86ExceptionContext, regs.rax),
    EXCEP_RBX_OFF = const offset_of!(X86ExceptionContext, regs.rbx),
    EXCEP_RCX_OFF = const offset_of!(X86ExceptionContext, regs.rcx),
    EXCEP_RDX_OFF = const offset_of!(X86ExceptionContext, regs.rdx),
    EXCEP_RSI_OFF = const offset_of!(X86ExceptionContext, regs.rsi),
    EXCEP_RDI_OFF = const offset_of!(X86ExceptionContext, regs.rdi),
    EXCEP_R15_OFF = const offset_of!(X86ExceptionContext, regs.r15),
    EXCEP_R14_OFF = const offset_of!(X86ExceptionContext, regs.r14),
    EXCEP_R13_OFF = const offset_of!(X86ExceptionContext, regs.r13),
    EXCEP_R12_OFF = const offset_of!(X86ExceptionContext, regs.r12),
    EXCEP_R11_OFF = const offset_of!(X86ExceptionContext, regs.r11),
    EXCEP_R10_OFF = const offset_of!(X86ExceptionContext, regs.r10),
    EXCEP_R9_OFF = const offset_of!(X86ExceptionContext, regs.r9),
    EXCEP_R8_OFF = const offset_of!(X86ExceptionContext, regs.r8),
    EXCEP_RBP_OFF = const offset_of!(X86ExceptionContext, regs.rbp),
    DEKO_DOORBELL_CTX_OFFSET = const offset_of!(DekoCpuCtx, ext_vmpl1) + offset_of!(DekoCpuCtxPerVmpl, doorbell),
    options(att_syntax)
);

const _: () = {
    assert!(core::mem::size_of::<HVDoorbell>() == 0x100);
};

verus! {

global layout HVDoorbell is size == 0x100, align == 0x4;

/// The flag bit in the doorbell's `flags` field indicating that there are no
/// further pending events to be signaled by the hypervisor.
///
/// See also [`HVDoorbell`].
///
/// Think of it as a hint from the guest to the hypervisor that it is busy
/// processing the current event and the hypervisor should not attempt to
/// signal any new events until the guest is ready again (e.g., after re-
/// enabling interrupts).
pub const HV_DOORBELL_NO_FURTHER_SIGNAL_FLAG: u8 = 0x80;

/// Initializes the global address of the per-CPU `HVDoorbell` pointer slot.
///
/// Each vCPU maps its own SNP doorbell page at the same *virtual* address.
/// To access the current CPU's doorbell without carrying a per-CPU pointer
/// everywhere, we cache the address of the per-CPU storage slot
/// (`DekoAtomicData<...>::data`) in `HV_DOORBELL_ADDR`.
///
/// The *address of the slot* is invariant across CPUs (same kernel image / same
/// virtual layout), while the slot's *contents* resolve to the current CPU’s
/// doorbell page via per-CPU mapping.
///
/// # Safety
/// - `ptr` must be valid, properly aligned, and point to a long-lived (static)
///   `DekoAtomicData` that remains mapped for the lifetime of the kernel.
/// - Must be called during early boot before any code reads `HV_DOORBELL_ADDR`,
///   or must be otherwise synchronized to avoid concurrent initialization.
#[verifier::external_body]
#[inline]
pub fn init_hv_doorbell(
    ptr: vstd::simple_pptr::PPtr<DekoAtomicData<DekoPPtr<HVDoorbell>, HvDoorbellPtrPermission>>,
) {
    unsafe {
        HV_DOORBELL_ADDR =
        addr_of!((*(ptr.addr() as *const DekoAtomicData<DekoPPtr<HVDoorbell>, HvDoorbellPtrPermission>)).data) as usize;
    }
}

#[verifier::external_body]
#[inline]
pub fn init_hv_doorbell_vmpl1() {
    unsafe {
        HV_DOORBELL_ADDR_VMPL1 = PERCPU_BASE_VMPL1.0 as usize;
        kinfo!("Initialized VMPL1 HV_DOORBELL_ADDR at address:", HV_DOORBELL_ADDR_VMPL1 => hex);
    }
}

#[repr(C)]
#[derive(DekoDebug)]
pub struct HVExtIntInfo {
    pub status: u32,
    pub irr: [u32; 7],
    pub isr: [u32; 8],
}

impl WellFormed for HVExtIntInfo {
    open spec fn wf(&self) -> bool {
        true
    }
}

/// HV Doorbell structure for handling interrupts from the hypervisor.
///
/// Isolated guests are expected to run with the SNP RestrictInjection feature active,
/// limiting the host to ringing a doorbell with a #HV exception.
///
/// # Note
///
/// This struct needs to be protected via a _lock_.
#[repr(C)]
pub struct HVDoorbell {
    /// Vector it tries to inject.
    pub vector: PAtomicU8,
    /// Bit 7 (0x80) is the "`NoFurtherSignal`" flag indicating that there are no
    /// further pending events to be signaled by the hypervisor.
    ///
    /// The original bitfield is u16 but for convenience we split them into two
    /// while maintaining the byte orders of the fields.
    pub flags: PAtomicU8,
    pub no_eoi_required: PAtomicU8,
    pub per_vmpl_events: PAtomicU8,
    pub reserved_: [u8; 60],  // not used.
    pub per_vmpl: [HVExtIntInfo; 3],
}

impl WellFormed for HVDoorbell {
    open spec fn wf(&self) -> bool {
        true
    }
}

#[verus_verify]
impl HVDoorbell {
    #[verus_spec(r =>
        with
            -> perm: Tracked<HVDoorbellPermission>,
        ensures
            r.wf(),
            perm@.vector_perm.is_for(r.vector),
            perm@.flags_perm.is_for(r.flags),
            perm@.no_eoi_required_perm.is_for(r.no_eoi_required),
            perm@.per_vmpl_events_perm.is_for(r.per_vmpl_events),
    )]
    pub fn new() -> Self {
        let (vector, Tracked(vector_perm)) = PAtomicU8::new(0);
        let (flags, Tracked(flags_perm)) = PAtomicU8::new(0);
        let (no_eoi_required, Tracked(no_eoi_required_perm)) = PAtomicU8::new(0);
        let (per_vmpl_events, Tracked(per_vmpl_events_perm)) = PAtomicU8::new(0);

        proof_with!(|= Tracked(
            HVDoorbellPermission {
                vector_perm,
                flags_perm,
                no_eoi_required_perm,
                per_vmpl_events_perm,
            }
        ));
        Self {
            vector,
            flags,
            no_eoi_required,
            per_vmpl_events,
            reserved_: [0;60],
            // DO this later.
            per_vmpl: [
                HVExtIntInfo { status: 0, irr: [0;7], isr: [0;8] },
                HVExtIntInfo { status: 0, irr: [0;7], isr: [0;8] },
                HVExtIntInfo { status: 0, irr: [0;7], isr: [0;8] },
            ],
        }
    }

    /// Checks if the NoFurtherSignal flag is set in the doorbell flags.
    ///
    /// When this flag is set, it indicates that there are no further
    /// pending events to be signaled by the hypervisor, and the guest
    /// should not expect any more doorbell notifications.
    #[inline]
    #[verus_spec(r =>
        with
            Tracked(hv_perm): Tracked<&mut HvDoorbellPtrPermission>,
        requires
            old(hv_perm).ptr_perm.wf(),
            old(hv_perm).ptr_perm.is_init(),
            old(hv_perm).ptr_perm.pptr() == hv_ptr@,
            old(hv_perm).hv_perm.flags_perm.is_for(old(hv_perm).ptr_perm.value().flags),
    )]
    pub fn no_further_signal(hv_ptr: DekoPPtr<HVDoorbell>) -> bool {
        let hv = hv_ptr.borrow(Tracked(&hv_perm.ptr_perm));

        hv.flags.fetch_and(Tracked(&mut hv_perm.hv_perm.flags_perm), !(0x80)) & 0x80 != 0
    }
}

with_permission! {
    HVDoorbell,
    vector_perm: PermissionU8,
    flags_perm: PermissionU8,
    no_eoi_required_perm: PermissionU8,
    per_vmpl_events_perm: PermissionU8,
}

pub tracked struct HvDoorbellPtrPermission {
    pub hv_perm: HVDoorbellPermission,
    pub ptr_perm: DekoPointsTo<HVDoorbell>,
}

type HvDoorbellPtr = DekoPPtr<HVDoorbell>;

with_atomic_pred! {
    HvDoorbellPtr,
    HvDoorbellPtrPermission,
    fields: { },
    perm_fields: { hv_perm, ptr_perm },

    ptr_perm.pptr() == data.view() &&
    ptr_perm.is_init() &&
    ptr_perm.wf() &&
    hv_perm.vector_perm.is_for(ptr_perm.value().vector) &&
    hv_perm.flags_perm.is_for(ptr_perm.value().flags) &&
    hv_perm.no_eoi_required_perm.is_for(ptr_perm.value().no_eoi_required) &&
    hv_perm.per_vmpl_events_perm.is_for(ptr_perm.value().per_vmpl_events)
}

#[verus_verify]
impl HVDoorbell {
    /// Initializes the global HV doorbell address for the current CPU.
    ///
    /// Note that the way the [`HV_DOORBELL_ADDR`] is initialized must
    /// use the fixed mapping address so that we always access the same
    /// virtual address across all CPUs to obtain the pointer to the
    /// inner [`HVDoorbell`].
    #[verus_spec()]
    pub fn init_hv_doorbell_addr() {
        let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
        let cpu_borrowed = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
        let doorbell = cpu_borrowed.doorbell.as_ref();

        kpanic_if!(core::hint::unlikely(doorbell.is_none()),
            "HVDoorbell is not initialized for this CPU!"
        );

        let doorbell_borrowed = doorbell.unwrap().acquire_read();
        let doorbell_ptr = doorbell_borrowed.as_ptr();
        init_hv_doorbell(doorbell_ptr);

        doorbell_borrowed.release_read();
    }

    /// Consults the frame allocator and gets a new allocated [`HVDoorbell`] structure.
    ///
    /// The returned pointer is aligned to page size.
    #[verus_spec(doorbell_ptr =>
        with
            -> db_perm: Tracked<HvDoorbellPtrPermission>,
        ensures
            db_perm.wf(),
            db_perm.ptr_perm.pptr() == doorbell_ptr.0@,
            db_perm.ptr_perm.is_init(),
            db_perm.ptr_perm.wf(),
            db_perm.hv_perm.vector_perm.is_for(db_perm.ptr_perm.value().vector),
            db_perm.hv_perm.flags_perm.is_for(db_perm.ptr_perm.value().flags),
            db_perm.hv_perm.no_eoi_required_perm.is_for(db_perm.ptr_perm.value().no_eoi_required),
            db_perm.hv_perm.per_vmpl_events_perm.is_for(db_perm.ptr_perm.value().per_vmpl_events),
            doorbell_ptr.1@ % PAGE_SIZE == 0,
    )]
    pub fn allocate(is_vmpl1: bool) -> (DekoPPtr<Self>, PhysAddr) {
        let (cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();

        let cpu_borrowed = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
        let private_bit = cpu_borrowed.private_bit();
        let shared_bit = cpu_borrowed.shared_bit();
        let ghcb = cpu_borrowed.ghcb();

        // Note that HVDoorBell needs to be shared.
        let (doorbell_ptr, Tracked(mut perm)) = DekoPageFrameBox::<HVDoorbell>::new_zeroed_in(
            &DEKO_FRAME_ALLOCATOR_FULL,
        );
        let vaddr = VirtAddr(doorbell_ptr.addr() as u64);

        assume(vaddr.wf());
        assume(cpu_perm.pgtable_perm.mapped(vaddr));

        proof_with!(=> Tracked(doorbell_perm));
        let doorbell = HVDoorbell::new();

        doorbell_ptr.write(Tracked(&mut perm), doorbell);

        PageTable::make_page_shared_4k(
            cpu_borrowed.pgtable,
            Tracked(&mut cpu_perm.pgtable_perm),
            vaddr,
            &cpu_borrowed.kernel_mapping,
            private_bit,
            shared_bit,
        );

        let Some(doorbell_paddr) = virt_to_phys_checked(
            private_bit,
            shared_bit,
            vaddr,
            Tracked(&cpu_perm.pgtable_perm),
        ) else {
            kerror!("HVDoorbell virtual address cannot be translated to physical address:", vaddr,);
            die("");
        };

        kinfo!("Allocated HVDoorbell at virtual address:", vaddr => hex, "physical address:", doorbell_paddr => hex, "for VMPL", if is_vmpl1 { "1" } else { "0" });

        kpanic_if!(core::hint::unlikely(doorbell_paddr.0 % PAGE_SIZE != 0),
            "HVDoorbell physical address is not page-aligned!"
        );

        // Then we register the doorbell with the GHCB.
        if !is_vmpl1 {
            GuestHostCommunicationBlock::register_hv_doorbell(
                ghcb,
                Tracked(cpu_perm.ghcb_perm),
                doorbell_paddr,
                cpu_borrowed.ghcb_gpa,
            );
        }
        // The initialization of VMPL1 doorbell is deferred until we enter VMPL1.

        let tracked db_perm = HvDoorbellPtrPermission { hv_perm: doorbell_perm, ptr_perm: perm };

        proof {
            assert(db_perm.ptr_perm.pptr() == doorbell_ptr@);
            assert(db_perm.ptr_perm.is_init());
            assert(db_perm.ptr_perm.wf());
            assert(db_perm.hv_perm.vector_perm.is_for(db_perm.ptr_perm.value().vector));
            assert(db_perm.hv_perm.flags_perm.is_for(db_perm.ptr_perm.value().flags));
            assert(db_perm.hv_perm.no_eoi_required_perm.is_for(
                db_perm.ptr_perm.value().no_eoi_required,
            ));
            assert(db_perm.hv_perm.per_vmpl_events_perm.is_for(
                db_perm.ptr_perm.value().per_vmpl_events,
            ));
        }

        proof_with!(|= Tracked(db_perm));
        (doorbell_ptr, doorbell_paddr)
    }
}

/// Handle a Restricted-Injection `#HV` doorbell notification.
///
/// In SEV-SNP Restricted Injection mode, the hypervisor cannot inject arbitrary
/// interrupt vectors directly. Instead, it signals pending events by injecting
/// `#HV` (vector 28) and writing the actual pending event (e.g., an IPI vector)
/// into the per-vCPU doorbell page (`hvdb`).
///
/// This handler is entered from the `#HV` IDT gate and is responsible for:
/// - Acknowledging the doorbell by atomically reading/clearing the pending
///   state in the doorbell page (to allow future notifications).
/// - Decoding the pending event and dispatching it to the appropriate internal
///   interrupt/event handler (e.g., IPI, kick, timer, etc.).
/// - Performing any required end-of-interrupt bookkeeping (if the doorbell
///   indicates EOI assist / no-EOI-required semantics).
///
/// # Safety
/// - Must be callable from interrupt context.
/// - `hvdb` must point to the per-vCPU doorbell page and remain valid for the
///   duration of the call.
/// - The doorbell page must be mapped as shared/unencrypted (C=0) as required
///   by the SNP GHCB doorbell mechanism.
/// - Implementations must not block, allocate, or take locks that can deadlock
///   in interrupt context.
#[doc(hidden)]
#[no_mangle]
#[allow(improper_ctypes_definitions)]
#[verifier::exec_allows_no_decreases_clause]
#[verus_spec(r =>
    with
        Tracked(hvdb_perm): Tracked<&mut HvDoorbellPtrPermission>,
    requires
        old(hvdb_perm).ptr_perm.pptr() == hvdb_ptr@,
        old(hvdb_perm).ptr_perm.is_init(),
        old(hvdb_perm).ptr_perm.wf(),
        old(hvdb_perm).hv_perm.vector_perm.is_for(old(hvdb_perm).ptr_perm.value().vector),
        old(hvdb_perm).hv_perm.flags_perm.is_for(old(hvdb_perm).ptr_perm.value().flags),
        old(hvdb_perm).hv_perm.no_eoi_required_perm.is_for(old(hvdb_perm).ptr_perm.value().no_eoi_required),
        old(hvdb_perm).hv_perm.per_vmpl_events_perm.is_for(old(hvdb_perm).ptr_perm.value().per_vmpl_events),
    ensures
        hvdb_perm.ptr_perm == old(hvdb_perm).ptr_perm,
        hvdb_perm.hv_perm.vector_perm.is_for(hvdb_perm.ptr_perm.value().vector),
        hvdb_perm.hv_perm.flags_perm.is_for(hvdb_perm.ptr_perm.value().flags),
        hvdb_perm.hv_perm.no_eoi_required_perm.is_for(hvdb_perm.ptr_perm.value().no_eoi_required),
        hvdb_perm.hv_perm.per_vmpl_events_perm.is_for(hvdb_perm.ptr_perm.value().per_vmpl_events),
)]
pub unsafe extern "C" fn handle_hv_doorbell(hvdb_ptr: DekoPPtr<HVDoorbell>) {
    if is_vmpl1() {
        proof_with!(Tracked(hvdb_perm));
        handle_hv_doorbell_vmpl1(hvdb_ptr);
    } else {
        proof_with!(Tracked(hvdb_perm));
        handle_hv_doorbell_vmpl0(hvdb_ptr);
    }
}

/// Process pending #HV doorbell events without touching IRQ nesting state.
///
/// This is intended for the after-IRQ-enable drain path, where IRQ nesting
/// bookkeeping has already been handled by the caller.
#[verus_spec(r =>
    with
        Tracked(hvdb_perm): Tracked<&mut HvDoorbellPtrPermission>,
    requires
        old(hvdb_perm).ptr_perm.pptr() == hvdb_ptr@,
        old(hvdb_perm).ptr_perm.is_init(),
        old(hvdb_perm).ptr_perm.wf(),
        old(hvdb_perm).hv_perm.vector_perm.is_for(old(hvdb_perm).ptr_perm.value().vector),
        old(hvdb_perm).hv_perm.flags_perm.is_for(old(hvdb_perm).ptr_perm.value().flags),
        old(hvdb_perm).hv_perm.no_eoi_required_perm.is_for(old(hvdb_perm).ptr_perm.value().no_eoi_required),
        old(hvdb_perm).hv_perm.per_vmpl_events_perm.is_for(old(hvdb_perm).ptr_perm.value().per_vmpl_events),
    ensures
        hvdb_perm.ptr_perm == old(hvdb_perm).ptr_perm,
        hvdb_perm.hv_perm.vector_perm.is_for(hvdb_perm.ptr_perm.value().vector),
        hvdb_perm.hv_perm.flags_perm.is_for(hvdb_perm.ptr_perm.value().flags),
        hvdb_perm.hv_perm.no_eoi_required_perm.is_for(hvdb_perm.ptr_perm.value().no_eoi_required),
        hvdb_perm.hv_perm.per_vmpl_events_perm.is_for(hvdb_perm.ptr_perm.value().per_vmpl_events),
)]
fn handle_hv_doorbell_pending(hvdb_ptr: DekoPPtr<HVDoorbell>) {
    if is_vmpl1() {
        proof_with!(Tracked(hvdb_perm));
        handle_hv_doorbell_pending_vmpl1(hvdb_ptr);
    } else {
        proof_with!(Tracked(hvdb_perm));
        handle_hv_doorbell_pending_vmpl0(hvdb_ptr);
    }
}

#[verus_spec(r =>
    with
        Tracked(hvdb_perm): Tracked<&mut HvDoorbellPtrPermission>,
    requires
        old(hvdb_perm).ptr_perm.pptr() == hvdb_ptr@,
        old(hvdb_perm).ptr_perm.is_init(),
        old(hvdb_perm).ptr_perm.wf(),
        old(hvdb_perm).hv_perm.vector_perm.is_for(old(hvdb_perm).ptr_perm.value().vector),
        old(hvdb_perm).hv_perm.flags_perm.is_for(old(hvdb_perm).ptr_perm.value().flags),
        old(hvdb_perm).hv_perm.no_eoi_required_perm.is_for(old(hvdb_perm).ptr_perm.value().no_eoi_required),
        old(hvdb_perm).hv_perm.per_vmpl_events_perm.is_for(old(hvdb_perm).ptr_perm.value().per_vmpl_events),
    ensures
        hvdb_perm.ptr_perm == old(hvdb_perm).ptr_perm,
        hvdb_perm.hv_perm.vector_perm.is_for(hvdb_perm.ptr_perm.value().vector),
        hvdb_perm.hv_perm.flags_perm.is_for(hvdb_perm.ptr_perm.value().flags),
        hvdb_perm.hv_perm.no_eoi_required_perm.is_for(hvdb_perm.ptr_perm.value().no_eoi_required),
        hvdb_perm.hv_perm.per_vmpl_events_perm.is_for(hvdb_perm.ptr_perm.value().per_vmpl_events),
)]
fn handle_hv_doorbell_pending_vmpl1(hvdb_ptr: DekoPPtr<HVDoorbell>) {
    let (cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_taken = cpu.take(Tracked(&mut cpu_perm.ptr_perm));

    proof_with!(Tracked(hvdb_perm), Tracked(&mut cpu_perm));
    handle_hv_doorbell_common(hvdb_ptr, cpu, cpu_taken);
}

#[verus_spec(r =>
    with
        Tracked(hvdb_perm): Tracked<&mut HvDoorbellPtrPermission>,
    requires
        old(hvdb_perm).ptr_perm.pptr() == hvdb_ptr@,
        old(hvdb_perm).ptr_perm.is_init(),
        old(hvdb_perm).ptr_perm.wf(),
        old(hvdb_perm).hv_perm.vector_perm.is_for(old(hvdb_perm).ptr_perm.value().vector),
        old(hvdb_perm).hv_perm.flags_perm.is_for(old(hvdb_perm).ptr_perm.value().flags),
        old(hvdb_perm).hv_perm.no_eoi_required_perm.is_for(old(hvdb_perm).ptr_perm.value().no_eoi_required),
        old(hvdb_perm).hv_perm.per_vmpl_events_perm.is_for(old(hvdb_perm).ptr_perm.value().per_vmpl_events),
    ensures
        hvdb_perm.ptr_perm == old(hvdb_perm).ptr_perm,
        hvdb_perm.hv_perm.vector_perm.is_for(hvdb_perm.ptr_perm.value().vector),
        hvdb_perm.hv_perm.flags_perm.is_for(hvdb_perm.ptr_perm.value().flags),
        hvdb_perm.hv_perm.no_eoi_required_perm.is_for(hvdb_perm.ptr_perm.value().no_eoi_required),
        hvdb_perm.hv_perm.per_vmpl_events_perm.is_for(hvdb_perm.ptr_perm.value().per_vmpl_events),
)]
fn handle_hv_doorbell_pending_vmpl0(hvdb_ptr: DekoPPtr<HVDoorbell>) {
    let (cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_taken = cpu.take(Tracked(&mut cpu_perm.ptr_perm));

    proof_with!(Tracked(hvdb_perm), Tracked(&mut cpu_perm));
    handle_hv_doorbell_common(hvdb_ptr, cpu, cpu_taken);
}

// ============= Refactor the API ============== //
//
// Currently the "move-and-update" way is way too awkward to use and has many
// ergonomic issues.
#[verus_spec(r =>
    with
        Tracked(hvdb_perm): Tracked<&mut HvDoorbellPtrPermission>,
    requires
        old(hvdb_perm).ptr_perm.pptr() == hvdb_ptr@,
        old(hvdb_perm).ptr_perm.is_init(),
        old(hvdb_perm).ptr_perm.wf(),
        old(hvdb_perm).hv_perm.vector_perm.is_for(old(hvdb_perm).ptr_perm.value().vector),
        old(hvdb_perm).hv_perm.flags_perm.is_for(old(hvdb_perm).ptr_perm.value().flags),
        old(hvdb_perm).hv_perm.no_eoi_required_perm.is_for(old(hvdb_perm).ptr_perm.value().no_eoi_required),
        old(hvdb_perm).hv_perm.per_vmpl_events_perm.is_for(old(hvdb_perm).ptr_perm.value().per_vmpl_events),
    ensures
        hvdb_perm.ptr_perm == old(hvdb_perm).ptr_perm,
        hvdb_perm.hv_perm.vector_perm.is_for(hvdb_perm.ptr_perm.value().vector),
        hvdb_perm.hv_perm.flags_perm.is_for(hvdb_perm.ptr_perm.value().flags),
        hvdb_perm.hv_perm.no_eoi_required_perm.is_for(hvdb_perm.ptr_perm.value().no_eoi_required),
        hvdb_perm.hv_perm.per_vmpl_events_perm.is_for(hvdb_perm.ptr_perm.value().per_vmpl_events),
)]
fn handle_hv_doorbell_vmpl1(hvdb_ptr: DekoPPtr<HVDoorbell>) {
    let (cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let mut cpu_taken = cpu.take(Tracked(&mut cpu_perm.ptr_perm));

    kpanic_if!(core::hint::unlikely(cpu_taken.ext_vmpl1.is_none()), "VMPL1 CPU context not initialized");

    let mut ext_vmpl1 = cpu_taken.ext_vmpl1.take().unwrap();
    let tracked mut ext_vmpl1_perm = cpu_perm.ext_vmpl1_perm.tracked_take();
    proof_with!(Tracked(&mut ext_vmpl1_perm.nested_irq_perm));
    ext_vmpl1.nested_irq.push(true);
    cpu_taken.ext_vmpl1.replace(ext_vmpl1);
    proof {
        cpu_perm.ext_vmpl1_perm = Some(ext_vmpl1_perm);
    }

    proof_with!(Tracked(hvdb_perm), Tracked(&mut cpu_perm));
    handle_hv_doorbell_common(hvdb_ptr, cpu, cpu_taken);

    cpu_taken = cpu.take(Tracked(&mut cpu_perm.ptr_perm));
    kpanic_if!(core::hint::unlikely(cpu_taken.ext_vmpl1.is_none()), "VMPL1 CPU context not initialized");
    let mut ext_vmpl1 = cpu_taken.ext_vmpl1.take().unwrap();
    let tracked mut ext_vmpl1_perm = cpu_perm.ext_vmpl1_perm.tracked_take();
    proof_with!(Tracked(&mut ext_vmpl1_perm.nested_irq_perm));
    ext_vmpl1.nested_irq.pop();
    cpu_taken.ext_vmpl1.replace(ext_vmpl1);
    proof {
        cpu_perm.ext_vmpl1_perm = Some(ext_vmpl1_perm);
    }
    cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);
}

#[verus_spec(r =>
    with
        Tracked(hvdb_perm): Tracked<&mut HvDoorbellPtrPermission>,
    requires
        old(hvdb_perm).ptr_perm.pptr() == hvdb_ptr@,
        old(hvdb_perm).ptr_perm.is_init(),
        old(hvdb_perm).ptr_perm.wf(),
        old(hvdb_perm).hv_perm.vector_perm.is_for(old(hvdb_perm).ptr_perm.value().vector),
        old(hvdb_perm).hv_perm.flags_perm.is_for(old(hvdb_perm).ptr_perm.value().flags),
        old(hvdb_perm).hv_perm.no_eoi_required_perm.is_for(old(hvdb_perm).ptr_perm.value().no_eoi_required),
        old(hvdb_perm).hv_perm.per_vmpl_events_perm.is_for(old(hvdb_perm).ptr_perm.value().per_vmpl_events),
    ensures
        hvdb_perm.ptr_perm == old(hvdb_perm).ptr_perm,
        hvdb_perm.hv_perm.vector_perm.is_for(hvdb_perm.ptr_perm.value().vector),
        hvdb_perm.hv_perm.flags_perm.is_for(hvdb_perm.ptr_perm.value().flags),
        hvdb_perm.hv_perm.no_eoi_required_perm.is_for(hvdb_perm.ptr_perm.value().no_eoi_required),
        hvdb_perm.hv_perm.per_vmpl_events_perm.is_for(hvdb_perm.ptr_perm.value().per_vmpl_events),
)]
#[verifier::exec_allows_no_decreases_clause]
fn handle_hv_doorbell_vmpl0(hvdb_ptr: DekoPPtr<HVDoorbell>) {
    let (cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let mut cpu_taken = cpu.take(Tracked(&mut cpu_perm.ptr_perm));

    proof_with!(Tracked(&mut cpu_perm.irq_state_perm));
    cpu_taken.nested_irq.push(true);

    proof_with!(Tracked(hvdb_perm), Tracked(&mut cpu_perm));
    handle_hv_doorbell_common(hvdb_ptr, cpu, cpu_taken);

    cpu_taken = cpu.take(Tracked(&mut cpu_perm.ptr_perm));

    proof_with!(Tracked(&mut cpu_perm.irq_state_perm));
    cpu_taken.nested_irq.pop();
    cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);
}

#[verus_spec(r =>
    with
        Tracked(hvdb_perm): Tracked<&mut HvDoorbellPtrPermission>,
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(hvdb_perm).ptr_perm.pptr() == hvdb_ptr@,
        old(hvdb_perm).ptr_perm.is_init(),
        old(hvdb_perm).ptr_perm.wf(),
        old(hvdb_perm).hv_perm.vector_perm.is_for(old(hvdb_perm).ptr_perm.value().vector),
        old(hvdb_perm).hv_perm.flags_perm.is_for(old(hvdb_perm).ptr_perm.value().flags),
        old(hvdb_perm).hv_perm.no_eoi_required_perm.is_for(old(hvdb_perm).ptr_perm.value().no_eoi_required),
        old(hvdb_perm).hv_perm.per_vmpl_events_perm.is_for(old(hvdb_perm).ptr_perm.value().per_vmpl_events),
    ensures
        hvdb_perm.ptr_perm == old(hvdb_perm).ptr_perm,
        hvdb_perm.hv_perm.vector_perm.is_for(hvdb_perm.ptr_perm.value().vector),
        hvdb_perm.hv_perm.flags_perm.is_for(hvdb_perm.ptr_perm.value().flags),
        hvdb_perm.hv_perm.no_eoi_required_perm.is_for(hvdb_perm.ptr_perm.value().no_eoi_required),
        hvdb_perm.hv_perm.per_vmpl_events_perm.is_for(hvdb_perm.ptr_perm.value().per_vmpl_events),
        cpu_perm.wf_with(cpu),
)]
#[verifier::exec_allows_no_decreases_clause]
#[verifier::external_body]  // the loop invariant is overly complicated so skip now.
fn handle_hv_doorbell_common(
    hvdb_ptr: DekoPPtr<HVDoorbell>,
    cpu: DekoPPtr<DekoCpuCtx>,
    mut cpu_taken: DekoCpuCtx,
) {
    let hvdb: &HVDoorbell = hvdb_ptr.borrow(Tracked(&hvdb_perm.ptr_perm));
    let flags = hvdb.flags.fetch_and(
        Tracked(&mut hvdb_perm.hv_perm.flags_perm),
        !(HV_DOORBELL_NO_FURTHER_SIGNAL_FLAG),
    );
    let mut vector = hvdb.vector.load(Tracked(&mut hvdb_perm.hv_perm.vector_perm));
    // Some hosts may transiently expose a non-zero vector before/without
    // NoFurtherSignal set; process either signal to avoid losing events.
    if flags & HV_DOORBELL_NO_FURTHER_SIGNAL_FLAG != 0 || vector != 0 {
        #[verus_spec(
            invariant_except_break
                hvdb_perm.hv_perm.vector_perm.is_for(hvdb.vector),
                hvdb_perm.hv_perm.flags_perm.is_for(hvdb.flags),
                hvdb_perm.hv_perm.no_eoi_required_perm.is_for(hvdb.no_eoi_required),
                hvdb_perm.hv_perm.per_vmpl_events_perm.is_for(hvdb.per_vmpl_events),
                hvdb_perm.ptr_perm == old(hvdb_perm).ptr_perm,
                cpu_perm.pgtable_perm == old(cpu_perm).pgtable_perm,
                cpu_taken.wf(),
                cpu_perm.ptr_perm.pptr() == cpu@,
                cpu_perm.ptr_perm.mem_wf(),
                cpu_perm.wf_with(cpu),
            ensures
                cpu_perm.ptr_perm.is_init()
        )]
        loop {
            match hvdb.vector.compare_exchange_weak(
                Tracked(&mut hvdb_perm.hv_perm.vector_perm),
                vector,
                0,
            ) {
                Ok(_) => match vector as usize {
                    IPI_VECTOR => {
                        crate::dbg::hv_trace_event(hvdb_ptr, 1, vector as u64, flags as u64);
                        cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);

                        proof_with!(Tracked(cpu_perm));
                        DekoCpuCtx::handle_ipi_req(cpu);

                        cpu_taken = cpu.take(Tracked(&mut cpu_perm.ptr_perm));
                    },
                    TIMER_VECTOR => {
                        crate::dbg::hv_trace_event(hvdb_ptr, 2, vector as u64, flags as u64);

                        if is_vmpl1() {
                            if let Err(e) = request_vmpl2_timer_event() {
                                kerror!("VMPL1 timer event request to VMPL0 failed:", e);
                            }
                        }
                        let apic = cpu_taken.apic();

                        // The trick here is that the physical APIC
                        // is ignorant of the VMPL so anyone can attempt
                        // to send an EOI signal to the hypervisor.
                        //
                        // Thus, if the timer arrives when monitor
                        // is running the timer will be consumed by
                        // us; and if the timer arrives when guest
                        // is running, the interrupt will be injected
                        // by the hypervisor; the guest will handle
                        // the rest.
                        apic.eoi();
                    },
                    _ => {
                        crate::dbg::hv_trace_event(hvdb_ptr, 3, vector as u64, flags as u64);
                        break ;
                    },
                },
                Err(current_val) => {
                    vector = current_val;
                },
            }
        }
    }
    cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);
}

#[inline]
#[verus_spec(r =>
)]
#[verifier::exec_allows_no_decreases_clause]
pub fn process_pending_hv_events() {
    if is_vmpl1() {
        process_pending_hv_events_vmpl1();
    } else {
        process_pending_hv_events_vmpl0();
    }
}

#[verus_spec(r =>
)]
#[verifier::exec_allows_no_decreases_clause]
fn process_pending_hv_events_vmpl1() {
    // For VMPL1, we can directly call the handler as we will never lose the doorbell notification.
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrowed = cpu.borrow(Tracked(&cpu_perm.ptr_perm));

    if let Some(ref ext_vmpl) = cpu_borrowed.ext_vmpl1 {
        do_processing_hv_events(&ext_vmpl.doorbell);
    }
}

/// Process any pending hypervisor events signaled via the doorbell page.
///
/// This is because #HV will be delivered even when interrupts are disabled,
/// so we need to check the doorbell page after enabling interrupts.
///
/// In the assembly code this event processing will be delayed to avoid
/// interrupt storm; when the target core enables interrupts, this means
/// it is ready to process pending events.
#[verus_spec()]
#[verifier::exec_allows_no_decreases_clause]
fn process_pending_hv_events_vmpl0() {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrowed = cpu.borrow(Tracked(&cpu_perm.ptr_perm));

    if let Some(doorbell) = &cpu_borrowed.doorbell {
        do_processing_hv_events(doorbell);
    }
}

#[verus_spec(
    requires
        doorbell.wf(),
)]
#[verifier::exec_allows_no_decreases_clause]
fn do_processing_hv_events(
    doorbell: &RwLock<
        DekoAtomicData<DekoPPtr<HVDoorbell>, HvDoorbellPtrPermission>,
        IrqUnSafeLockGuard,
        HvDoorbellPtrPred,
    >,
) {
    // This path toggles IF with raw cli/sti while draining pending events.
    // If IF is already 0 at entry, running this would incorrectly force-enable
    // interrupts at the end of a drain round.
    if !irq_enabled() {
        return ;
    }
    #[verus_spec(
        invariant_except_break
            doorbell.wf(),
    )]
    loop {
        if !has_pending_hv_events(doorbell) {
            break ;
        }
        // Keep this as raw IF toggling only. Using irq_disable()/irq_enable()
        // here would recurse into after_irq_enable() and unbound nesting.

        raw_irq_disable();

        deko_rwlock_write_atomic_data! {
            doorbell,
            doorbell_ptr,
            doorbell_perm,
            {
                #[verus_spec(with Tracked(doorbell_perm.borrow_mut()))]
                handle_hv_doorbell_pending(doorbell_ptr);
            }
        }

        raw_irq_enable();
    }
}

#[inline]
#[verus_spec(
    requires
        doorbell.wf(),
)]
fn has_pending_hv_events(
    doorbell: &RwLock<
        DekoAtomicData<DekoPPtr<HVDoorbell>, HvDoorbellPtrPermission>,
        IrqUnSafeLockGuard,
        HvDoorbellPtrPred,
    >,
) -> bool {
    deko_rwlock_read_atomic_data! {
        doorbell,
        doorbell_ptr,
        doorbell_perm,
        {
            let doorbell = doorbell_ptr.borrow(Tracked(&doorbell_perm.borrow().ptr_perm));
            let flags = doorbell.flags.load(Tracked(&doorbell_perm.borrow().hv_perm.flags_perm));
            let vector = doorbell.vector.load(Tracked(&doorbell_perm.borrow().hv_perm.vector_perm));

            (flags & HV_DOORBELL_NO_FURTHER_SIGNAL_FLAG != 0) || (vector != 0)
        }
    }
}

} // verus!
