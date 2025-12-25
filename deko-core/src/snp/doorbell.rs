use core::ptr::addr_of;

use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::address::VirtAddr;
use deko_std::mem::PAGE_SIZE;
use deko_std::ptr::{DekoPPtr, DekoPPtrPred, DekoPointsTo};
use deko_std::sync::{DekoAtomicData, DekoRwLock};
use deko_std::wf::WellFormed;
use deko_std::{boxed_ptr, with_permission};
use vstd::prelude::*;

use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::mm::paging::PageTable;
use crate::mm::{virt_to_phys, virt_to_phys_checked, DEKO_FRAME_ALLOCATOR};
use crate::snp::ghcb::{current_ghcb, GuestHostCommunicationBlock};
use crate::{die, kerror, kpanic_if};

extern "C" {
    // exclusive.
    #[link_section = ".data"]
    pub static mut HV_DOORBELL_ADDR: usize;
}

verus! {

/// This is a trick to obtain the different HV doorbell pages from the same virtual address.
/// This is because CPU will always map itself to the fixed address and the address of the
/// doorbell's pointer remains the same across different CPUs.
#[verifier::external_body]
#[inline]
pub fn init_hv_doorbell(
    ptr: vstd::simple_pptr::PPtr<DekoAtomicData<DekoPPtr<HVDoorbell>, DekoPointsTo<HVDoorbell>>>,
) {
    unsafe {
        HV_DOORBELL_ADDR =
        addr_of!((*(ptr.addr() as *const DekoAtomicData<DekoPPtr<HVDoorbell>, DekoPointsTo<HVDoorbell>>)).data) as usize;
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
    #[verus_spec()]
    pub fn allocate() {
        let (cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();

        let cpu_borrowed = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
        let private_bit = cpu_borrowed.private_bit();
        let shared_bit = cpu_borrowed.shared_bit();
        let ghcb = cpu_borrowed.ghcb();

        // Note that HVDoorBell needs to be shared.
        let (doorbell_ptr, Tracked(perm)) = boxed_ptr!(HVDoorbell, &DEKO_FRAME_ALLOCATOR.0);
        let vaddr = VirtAddr::new(doorbell_ptr.addr() as u64);

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

        let mut cpu_taken = cpu.take(Tracked(&mut cpu_perm.ptr_perm));
        cpu_taken.doorbell = Some(
            DekoRwLock::new(
                DekoAtomicData::new_with(doorbell_ptr, Tracked(perm)),
                (),
                Ghost(DekoPPtrPred {  }),
            ),
        );

        init_hv_doorbell(
            {
                let handle = cpu_taken.doorbell.as_ref().unwrap().acquire_read();
                let ptr = handle.as_ptr();
                handle.release_read();
                ptr
            },
        );

        cpu.put(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);
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
    crate::kinfo!("test");

    // For now, we just panic.
    kpanic_if!(true, "Received HV Doorbell interrupt! Bye");
}

} // verus!
