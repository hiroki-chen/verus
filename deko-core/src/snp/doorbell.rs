use core::ptr::addr_of;

use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::address::VirtAddr;
use deko_std::mem::PAGE_SIZE;
use deko_std::ptr::{DekoPPtr, DekoPPtrPred, DekoPointsTo};
use deko_std::sync::{DekoAtomicData, DekoRwLock};
use deko_std::wf::WellFormed;
use deko_std::{boxed_ptr, with_permission};
use vstd::atomic::{PAtomicU8, PermissionU8};
use vstd::prelude::*;

use crate::cpu::apic::Apic;
use crate::cpu::idt::IPI_VECTOR;
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::mm::paging::PageTable;
use crate::mm::{virt_to_phys, virt_to_phys_checked, DEKO_FRAME_ALLOCATOR_FULL};
use crate::snp::ghcb::{current_ghcb, GuestHostCommunicationBlock};
use crate::{die, kdebug, kerror, kinfo, kpanic_if, kwarn};

extern "C" {
    // exclusive.
    #[link_section = ".data"]
    pub static mut HV_DOORBELL_ADDR: usize;
}

verus! {

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
    pub vector: PAtomicU8,
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

    #[verus_spec(r =>
        with
            Tracked(hv_perm): Tracked<&HvDoorbellPtrPermission>,
        requires
            hv_perm.ptr_perm.wf(),
            hv_perm.ptr_perm.is_init(),
            hv_perm.ptr_perm.pptr() == hv_ptr@,
            hv_perm.hv_perm.flags_perm.is_for(hv_perm.ptr_perm.value().flags),
    )]
    pub fn no_further_signal(hv_ptr: DekoPPtr<HVDoorbell>) -> bool {
        let hv = hv_ptr.borrow(Tracked(&hv_perm.ptr_perm));

        hv.flags.load(Tracked(&hv_perm.hv_perm.flags_perm)) & 0x80 == 0
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
    fn init_hv_doorbell_addr() {
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
    #[verus_spec()]
    pub fn allocate() {
        let (cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();

        let cpu_borrowed = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
        let private_bit = cpu_borrowed.private_bit();
        let shared_bit = cpu_borrowed.shared_bit();
        let ghcb = cpu_borrowed.ghcb();

        // Note that HVDoorBell needs to be shared.
        let (doorbell_ptr, Tracked(perm)) = boxed_ptr!(HVDoorbell, &DEKO_FRAME_ALLOCATOR_FULL);
        let vaddr = VirtAddr::new(doorbell_ptr.addr() as u64);

        proof_with!(=> Tracked(doorbell_perm));
        let doorbell = HVDoorbell::new();

        PageTable::make_page_shared_4k(
            cpu_borrowed.pgtable,
            Tracked(&mut cpu_perm.pgtable_perm),
            vaddr,
            &cpu_borrowed.kernel_mapping,
            private_bit,
            shared_bit,
        );

        crate::kinfo!("private_bit: ", private_bit, ", shared_bit: ", shared_bit, ", doorbell_vaddr: ", vaddr,);

        let Some(doorbell_paddr) = virt_to_phys_checked(
            private_bit,
            shared_bit,
            vaddr,
            Tracked(&cpu_perm.pgtable_perm),
        ) else {
            kerror!("HVDoorbell virtual address cannot be translated to physical address:", vaddr,);
            die("");
        };

        kpanic_if!(core::hint::unlikely(doorbell_paddr.0 % PAGE_SIZE != 0),
            "HVDoorbell physical address is not page-aligned!"
        );

        // Then we register the doorbell with the GHCB.
        GuestHostCommunicationBlock::register_hv_doorbell(
            ghcb,
            Tracked(cpu_perm.ghcb_perm),
            doorbell_paddr,
        );

        let tracked db_perm = HvDoorbellPtrPermission { hv_perm: doorbell_perm, ptr_perm: perm };
        let mut cpu_taken = cpu.take(Tracked(&mut cpu_perm.ptr_perm));
        cpu_taken.doorbell = Some(
            DekoRwLock::new(
                DekoAtomicData::new_with(doorbell_ptr, Tracked(db_perm)),
                (),
                Ghost(HvDoorbellPtrPred {  }),
            ),
        );

        cpu.put(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);

        Self::init_hv_doorbell_addr();
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
        Tracked(hvdb_perm): Tracked<HvDoorbellPtrPermission>,
    requires
        hvdb_perm.ptr_perm.pptr() == hvdb@,
        hvdb_perm.ptr_perm.is_init(),
        hvdb_perm.ptr_perm.wf(),

        hvdb_perm.hv_perm.vector_perm.is_for(hvdb_perm.ptr_perm.value().vector),
        hvdb_perm.hv_perm.flags_perm.is_for(hvdb_perm.ptr_perm.value().flags),
        hvdb_perm.hv_perm.no_eoi_required_perm.is_for(hvdb_perm.ptr_perm.value().no_eoi_required),
        hvdb_perm.hv_perm.per_vmpl_events_perm.is_for(hvdb_perm.ptr_perm.value().per_vmpl_events),
)]
pub unsafe extern "C" fn handle_hv_doorbell(hvdb: DekoPPtr<HVDoorbell>) {
    let tracked mut hvdb_perm = hvdb_perm;
    let hvdb = hvdb.borrow(Tracked(&hvdb_perm.ptr_perm));
    let vector = hvdb.vector.load(Tracked(&mut hvdb_perm.hv_perm.vector_perm));
    // Clear the flag.
    let flags = hvdb.flags.fetch_and(
        Tracked(&mut hvdb_perm.hv_perm.flags_perm),
        !(0x80)  /* NoFurtherSignal */
        ,
    );

    // Some sanity check for flags...
    loop
        invariant
            hvdb_perm.hv_perm.vector_perm.is_for(hvdb.vector),
    {
        match hvdb.vector.compare_exchange_weak(
            Tracked(&mut hvdb_perm.hv_perm.vector_perm),
            vector,
            0,
        ) {
            Ok(_) => {
                // Successfully cleared the doorbell.
                break ;
            },
            _ => {},
        }
    }

    match vector as usize {
        IPI_VECTOR => {
            // Dummy implementation for now.
            let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();

            proof_with!(Tracked(&cpu_perm));
            DekoCpuCtx::handle_ipi_req(cpu);
        },
        _ => {
            // Unknown vector.
            kwarn!("Unknown HV Doorbell vector received: ", vector, "as we only handle IPI");
        },
    }

    kdebug!("completed HV doorbell handling");
}

} // verus!
