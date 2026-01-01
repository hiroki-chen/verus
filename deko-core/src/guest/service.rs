use deko_macros::DekoDebug;
use deko_std::address::{create_paddr_range, PhysAddr, VirtAddr};
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto};
use deko_std::mem::{PAGE_SIZE, PAGE_SIZE_2M};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::cpu::{flush_tlb_global, DekoCpuCtxPermission};
use crate::guest::{DekoGuestRequestParams, DekoGuestServError, DekoGuestServResult};
use crate::imp::RmpFlags;
use crate::mm::vm::TempMapping;
use crate::mm::zero_page;
use crate::snp::{pvalidate, rmpadjust};
use crate::{kerror, kinfo};

verus! {

global layout DekoGuestPValidateReq is size == 8;

/// Represents a request structure for page validation operations.
///
/// The guest must place this request at the given physical address
/// before invoking the page validation service.
#[repr(C, packed)]
#[derive(Copy, Clone, DekoDebug)]
pub(super) struct DekoGuestPValidateReq {
    pub entries: u16,
    pub next: u16,
    #[deko(skip)]
    pub _reserved: u32,
}

pub const DEKO_SERVICE_REMAP_CA: u32 = 0x0;

pub const DEKO_SERVICE_PVALIDATE: u32 = 0x1;

pub const DEKO_SERVICE_CREATE_VCPU: u32 = 0x2;

pub const DEKO_SERVICE_DESTROY_VCPU: u32 = 0x3;

pub const DEKO_SERVICE_DEPOSIT_MEMORY: u32 = 0x4;

pub const DEKO_SERVICE_WITHDRAW_MEMORY: u32 = 0x5;

pub const DEKO_SERVICE_QUERY_PROTOCOL: u32 = 0x6;

/// Reads a reference to type `T` from the given guest virtual address.
///
/// TODO: This function requires more sophisticated safety checks and
/// isolation policies to ensure no arbitrary memory access occurs.
#[inline(always)]
#[verifier::external_body]
#[verus_spec(r =>
    requires
        // ?
)]
pub(super) fn read_guest_copied<T: Copy>(addr: VirtAddr) -> T {
    // SAFETY: The caller must ensure that the given
    // virtual address is valid and mapped on the
    // current core.
    unsafe { core::ptr::read_unaligned(addr.0 as *const T) }
}

#[inline(always)]
#[verifier::external_body]
#[verus_spec(r =>
    requires
        // ?
)]
pub(super) fn write_guest<T>(addr: VirtAddr, val: T) {
    // SAFETY: The caller must ensure that the given
    // virtual address is valid and mapped on the
    // current core.
    unsafe {
        core::ptr::write_unaligned(addr.0 as *mut T, val);
    }
}

/// Issues a pvalidate operation for a single page at the given physical address.
#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        paddr.wf(),
        old(cpu_perm).wf(),
    ensures
        cpu_perm.wf(),
)]
fn pvalidate_guest_one_page(paddr: PhysAddr) -> DekoGuestServResult<()> {
    broadcast use RmpFlags::lemma_each_bit_is_valid;

    proof {
        bit_u32_and_auto();
        bit_u64_and_auto();
    }

    // NOTE: the last four bits of the physical address
    // are used to indicate the page validation operations.
    let inner = paddr.0;
    let huge_page = (inner & 0x3) == 1;
    let validate = (inner & 0x4) == 4;

    // Currently we do not support huge page validation.
    if huge_page {
        kerror!("Guest pvalidate: huge page not supported:", paddr);
        return Err(DekoGuestServError::UnsupportedOperation);
    }
    let guest_pa = inner & !(PAGE_SIZE as u64 - 1);

    if core::hint::unlikely(guest_pa >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE) {
        kerror!("Guest pvalidate: physical address out of range:", guest_pa);
        return Err(DekoGuestServError::InvalidParameters);
    }
    proof {
        assert(guest_pa@ % PAGE_SIZE == 0) by (bit_vector)
            requires
                guest_pa == (inner & !((PAGE_SIZE as u64 - 1) as u64)),
                PAGE_SIZE == 0x1000,
        ;
    }
    // Need to first check if the physical address is
    // within the expected guest physical regions.
    if false {
        kerror!("Guest pvalidate: invalid physical address:", guest_pa);
        return Err(DekoGuestServError::InvalidParameters);
    }
    if let Some(temp_va) = TempMapping::new(create_paddr_range(PhysAddr(guest_pa), 1)) {
        assume(cpu_perm.pgtable_perm.mapped(temp_va.inner.start));

        let (r, has_changed) = pvalidate(
            temp_va.inner.start.0,
            PAGE_SIZE,
            true,
            Tracked(&mut cpu_perm.pgtable_perm),
        );

        if validate {
            zero_page(temp_va.inner.start);

            if rmpadjust(
                temp_va.inner.start,
                PAGE_SIZE,
                RmpFlags::rwx_guest_vmpl2(),
                Tracked(&mut cpu_perm.pgtable_perm),
            ) != 0 {
                return Err(DekoGuestServError::RmpAdjustFailed(PhysAddr(guest_pa)));
            }
            if r != 0 || !has_changed {
                // We do not allow twice validation of the same page.
                return Err(DekoGuestServError::InvalidParameters);
            }
        } else {
            crate::kwarn!("Not yet implementated");
        }

        Ok(())
    } else {
        Err(DekoGuestServError::MappingFailed(PhysAddr(guest_pa)))
    }
}

/// The guest is requesting for a page validation operation.
#[verifier::external_body]
#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
    ensures
        cpu_perm.wf(),
)]
fn handle_deko_service_pvalidate(params: &DekoGuestRequestParams) -> DekoGuestServResult<()> {
    crate::kinfo!("Handling guest pvalidate request", params);

    // During booting the page must not be aligned to PAGE_SIZE
    // but it must uphold the alignment requirement of x64 that
    // physical addresses must be aligned to qword.
    if core::hint::unlikely(params.rcx % (core::mem::size_of::<u64>() as u64) != 0) {
        kerror!("Guest pvalidate: unaligned physical address: ", params.rcx);
        return Err(DekoGuestServError::InvalidParameters);
    }
    // SANITY CHECK #2: Check if this request is valid.
    // i.e., if this gpa is within the valid guest
    // physical address range.

    if false {  /* Placeholder for now. */
        kerror!("Guest pvalidate: invalid physical address: ", params.rcx);
        return Err(DekoGuestServError::InvalidParameters);
    }
    // Make Verus happy.

    if core::hint::unlikely(params.rcx >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE) {
        kerror!("Guest pvalidate: physical address out of range: ", params.rcx);
        return Err(DekoGuestServError::InvalidParameters);
    }
    let offset = params.rcx % PAGE_SIZE as u64;
    let guest_pa = PhysAddr(params.rcx & !(PAGE_SIZE as u64 - 1));
    // Obtain the offset within the page.

    proof {
        let guest_pa = guest_pa@;
        let rcx = params.rcx;
        assert(guest_pa % PAGE_SIZE == 0 && guest_pa <= rcx) by (bit_vector)
            requires
                guest_pa == (rcx & !((PAGE_SIZE as u64 - 1) as u64)),
                PAGE_SIZE == 0x1000,
        ;
    }

    // Now we need to create a temporary mapping for the guest
    // physical address so that we can access the request structure.

    let paddr_range = create_paddr_range(guest_pa, 1);
    let temp_mapping = TempMapping::new(paddr_range);

    if let Some(temp_va) = temp_mapping {
        // SAFETY: We have verified that the guest_pa is valid
        // and the temporary mapping guarantees that we have
        // mapped the physical address on the current core.
        let mut guest_req = read_guest_copied::<DekoGuestPValidateReq>(
            VirtAddr(temp_va.inner.start.0 + offset),
        );

        let entries = guest_req.entries;
        let next = guest_req.next;

        let max_entries = (PAGE_SIZE - offset - core::mem::size_of::<
            DekoGuestPValidateReq,
        >() as u64) / core::mem::size_of::<u64>() as u64;

        // Sanitize the input parameter.
        if entries == 0 || entries > max_entries as u16 || entries <= next {
            return Err(DekoGuestServError::InvalidParameters);
        }
        // Now process the page validation entries.

        for i in next..entries
            invariant
                max_entries == (PAGE_SIZE - offset - core::mem::size_of::<
                    DekoGuestPValidateReq,
                >() as u64) / core::mem::size_of::<u64>() as int,
                next <= i <= entries <= max_entries,
                temp_va.wf(),
                temp_va.inner.start@ + PAGE_SIZE <= u64::MAX,
                entries as int >= 0,
                offset <= PAGE_SIZE,
                max_entries <= PAGE_SIZE,
                guest_req.next == i,
                core::mem::size_of::<u64>() == 8,
                core::mem::size_of::<DekoGuestPValidateReq>() == 8,
                cpu_perm.wf(),
        {
            // LAYOUT:
            // [ PADDING ]       [ DekoGuestPValidateReq ]                 [ u64 ] [ u64 entries... ]
            //            offset |<- size_of::<DekoGuestPValidateReq>() ->|       |<- u64 entries ->|
            let cur = temp_va.inner.start.0 + offset + core::mem::size_of::<
                DekoGuestPValidateReq,
            >() as u64 + (i as u64) * core::mem::size_of::<u64>() as u64;

            let this_entry = read_guest_copied::<u64>(VirtAddr(cur));
            let this_entry = PhysAddr(this_entry);

            proof_with!(Tracked(cpu_perm));
            let r = pvalidate_guest_one_page(this_entry);

            match r {
                Ok(()) => guest_req.next = guest_req.next + 1,
                Err(e) => return Err(e),
            };
        }

        // Write back to the guest request structure.
        write_guest(VirtAddr(temp_va.inner.start.0 + offset), guest_req);

        flush_tlb_global();

        Ok(())
    } else {
        kerror!("Guest pvalidate: failed to create temporary mapping for gpa: ", guest_pa.0);

        Err(DekoGuestServError::MappingFailed(guest_pa))
    }
}

/// Subroutine for handling DEKO service requests from the guest.
#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
    ensures
        cpu_perm.wf(),
)]
pub(super) fn handle_guest_exit_deko_service(
    req: u32,
    params: &mut DekoGuestRequestParams,
) -> DekoGuestServResult<()> {
    match req {
        DEKO_SERVICE_PVALIDATE => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_pvalidate(params)
        },
        _ => { Err(DekoGuestServError::UnknownRequest(req)) },
    }
}

} // verus!
