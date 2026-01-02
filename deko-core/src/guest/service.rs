use deko_macros::DekoDebug;
use deko_std::address::{create_paddr_range, PhysAddr, VirtAddr};
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto};
use deko_std::mem::{PAGE_SIZE, PAGE_SIZE_2M};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::cpu::{flush_tlb_global, DekoCpuCtxPermission};
use crate::guest::{
    DekoGuestRequestParams, DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode,
};
use crate::imp::RmpFlags;
use crate::mm::vm::TempMapping;
use crate::mm::zero_page;
use crate::snp::{pvalidate, rmpadjust, validate_vaddr_region};
use crate::{kdebug, kerror, kinfo, kwarn};

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
#[verifier::spinoff_prover]
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
    let guest_pa = inner & !(PAGE_SIZE as u64 - 1);
    let (len, page_size) = if huge_page {
        (512, PAGE_SIZE_2M)
    } else {
        (1, PAGE_SIZE)
    };

    if core::hint::unlikely(!huge_page && guest_pa >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE) || (
    huge_page && guest_pa >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE_2M) {
        kerror!("Guest pvalidate: physical address out of range:", guest_pa);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
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
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if let Some(temp_va) = TempMapping::new(create_paddr_range(PhysAddr(guest_pa), len)) {
        assume(cpu_perm.pgtable_perm.mapped_region(temp_va.inner));

        let (r, has_changed) = pvalidate(
            temp_va.inner.start.0,
            page_size,
            validate,
            Tracked(&mut cpu_perm.pgtable_perm),
        );

        if r != 0 {
            // if r != 0 then we possibly have a specific page size mismatch
            // or the page is already in the desired state.
            //
            // this leaves the guest for handling the rest.
            kdebug!("Guest pvalidate: pvalidate failed at gpa:", PhysAddr(guest_pa), "with return code:", r, " has_changed:", has_changed);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Other(r)));
        }
        if !has_changed {
            // Means ignore the carry flag even if the change has failed.
            if inner & 0x8 == 0x8 {
                return Ok(());
            } else {
                // No change has occurred.
                kdebug!("Guest pvalidate: no change has occurred for gpa:", PhysAddr(guest_pa) => hex);
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Other(0x10)));
            }
        }
        if validate {
            zero_page(temp_va.inner.start, len);

            if rmpadjust(
                temp_va.inner.start,
                page_size,
                RmpFlags::rwx_guest_vmpl2(),
                Tracked(&mut cpu_perm.pgtable_perm),
            ) != 0 {
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidReq));
            }
        }
        Ok(())
    } else {
        kerror!("Guest pvalidate: failed to create temporary mapping for gpa:", guest_pa => hex);
        Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy))
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
    crate::kdebug!("Handling guest pvalidate request", params);

    // During booting the page must not be aligned to PAGE_SIZE
    // but it must uphold the alignment requirement of x64 that
    // physical addresses must be aligned to qword.
    if core::hint::unlikely(params.rcx % (core::mem::size_of::<u64>() as u64) != 0) {
        kerror!("Guest pvalidate: unaligned physical address: ", params.rcx);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    // SANITY CHECK #2: Check if this request is valid.
    // i.e., if this gpa is within the valid guest
    // physical address range.

    if false {  /* Placeholder for now. */
        kerror!("Guest pvalidate: invalid physical address: ", params.rcx);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    // Make Verus happy.

    if core::hint::unlikely(params.rcx >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE) {
        kerror!("Guest pvalidate: physical address out of range: ", params.rcx);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
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
            kerror!("Guest pvalidate: invalid request parameters: entries=", entries, " next=", next, " max_entries=", max_entries);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        // Now process the page validation entries.

        let mut pvalidate_result = Ok(());
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

            pvalidate_result =
            #[verus_spec(with Tracked(cpu_perm))]
            pvalidate_guest_one_page(this_entry);

            match pvalidate_result {
                Ok(()) => guest_req.next = guest_req.next + 1,
                Err(e) => match e {
                    DekoGuestServError::SoftError(_) => break ,
                    DekoGuestServError::FatalError => return pvalidate_result,
                },
            };
        }

        // Write back to the guest request structure.
        write_guest(VirtAddr(temp_va.inner.start.0 + offset), guest_req);

        flush_tlb_global();

        pvalidate_result
    } else {
        kerror!("Guest pvalidate: failed to create temporary mapping for gpa: ", guest_pa.0);

        Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy))
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
    kdebug!("Handling guest deko service request: ", req, " with params: ", params);

    match req {
        DEKO_SERVICE_PVALIDATE => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_pvalidate(params)
        },
        _ => {
            kerror!("Unsupported deko service request: ", req);
            Err(DekoGuestServError::SoftError(DekoGuestServResultCode::UnsupportedProtocol))
        },
    }
}

} // verus!
