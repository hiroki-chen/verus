use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::address::VirtAddr;
use deko_std::mem::PAGE_SIZE;
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::wf::WellFormed;
use deko_std::{boxed_ptr, with_permission};
use vstd::prelude::*;

use crate::cpu::DekoCpuCtx;
use crate::kpanic_if;
use crate::mm::{virt_to_phys, DEKO_FRAME_ALLOCATOR};
use crate::snp::ghcb::{current_ghcb, GuestHostCommucationBlock};

verus! {

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
/// This struct needs to be protected via a lock.
#[repr(C)]
#[derive(DekoDebug)]
pub struct HVDoorbell {
    pub vector: u8,
    pub flags: u8,
    pub no_eoi_required: u8,
    pub per_vmpl_events: u8,
    pub reserved_: [u8; 60],
    pub per_vmpl: [HVExtIntInfo; 3],
}

impl WellFormed for HVDoorbell {
    open spec fn wf(&self) -> bool {
        true
    }
}

with_permission! {
    HVDoorbell,
}
// FIXME: This is probably not sufficient for now.


with_atomic_pred! {
    HVDoorbell,
    HVDoorbellPermission,
    fields: { },
    perm_fields: { },
    true
}

#[verus_verify]
impl HVDoorbell {
    /// Consults the frame allocator and gets a new allocated [`HVDoorbell`] structure.
    ///
    /// The returned pointer is aligned to page size.
    #[verus_spec(r =>
        with
            -> perm: Tracked<DekoPointsTo<Self>>,
        ensures
            perm@.wf(),
            perm@.pptr() == r@,
    )]
    pub fn allocate() -> DekoPPtr<Self> {
        let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();

        let cpu_borrowed = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
        let private_bit = cpu_borrowed.private_bit();
        let shared_bit = cpu_borrowed.shared_bit();
        let ghcb = cpu_borrowed.ghcb();

        let (doorbell_ptr, Tracked(perm)) = boxed_ptr!(HVDoorbell, &DEKO_FRAME_ALLOCATOR.0);
        let vaddr = VirtAddr::new(doorbell_ptr.addr() as u64);
        let doorbell_paddr = virt_to_phys(
            private_bit,
            shared_bit,
            vaddr,
            Tracked(&cpu_perm.pgtable_perm),
        );

        kpanic_if!(core::hint::unlikely(doorbell_paddr.0 % PAGE_SIZE != 0),
            "HVDoorbell physical address is not page-aligned!"
        );

        // Then we register the doorbell with the GHCB.
        GuestHostCommucationBlock::register_hv_doorbell(
            ghcb,
            Tracked(cpu_perm.ghcb_perm),
            doorbell_paddr,
        );

        proof_with!(|= Tracked(perm));
        doorbell_ptr
    }
}

#[doc(hidden)]
#[no_mangle]
#[allow(improper_ctypes_definitions)]
#[verus_spec(r =>
    with
        Tracked(hvdb_perm): Tracked<HVDoorbellPermission>,
    requires
        // hvdb_perm.wf(),
        // hvdb_perm.is_init(),
        // hvdb.pptr() == hvdb@,
)]
pub unsafe extern "C" fn handle_hv_doorbell(hvdb: DekoPPtr<HVDoorbell>) {
    // For now, we just panic.
    kpanic_if!(true, "Received HV Doorbell interrupt! Bye");
}

} // verus!
