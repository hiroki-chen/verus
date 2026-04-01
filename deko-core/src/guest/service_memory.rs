use deko_macros::DekoDebug;
use deko_std::address::{create_paddr_range, PhysAddr, VirtAddr};
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto};
use deko_std::mem::{PAGE_SIZE, PAGE_SIZE_2M};
use deko_std::wf::WellFormed;
use deko_std::{deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data};
use vstd::prelude::*;

use crate::cpu::{DekoCpuCtxPermission, PERCPU_AREAS};
use crate::guest::service::{read_guest_copied, write_guest};
use crate::guest::{
    valid_guest_page, DekoGuestRequestParams, DekoGuestServError, DekoGuestServResult,
    DekoGuestServResultCode,
};
use crate::imp::RmpFlags;
use crate::mm::vm::TempMapping;
use crate::mm::{check_within_guest_mmap, zero_page};
use crate::snp::{pvalidate, rmpadjust};
use crate::{kdebug, kerror};

verus! {

global layout DekoGuestPValidateReq is size == 8;

/// Represents a request structure for page validation operations.
///
/// The guest must place this request at the given physical address
/// before invoking the page validation service.
#[repr(C, packed)]
#[derive(Copy, Clone, DekoDebug)]
pub(crate) struct DekoGuestPValidateReq {
    pub entries: u16,
    pub next: u16,
    #[deko(skip)]
    pub _reserved: u32,
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
        final(cpu_perm).wf(),
        final(cpu_perm).ptr_perm.value().cpu_id == old(cpu_perm).ptr_perm.value().cpu_id,
)]
fn pvalidate_guest_one_page(paddr: PhysAddr) -> DekoGuestServResult<()> {
    broadcast use RmpFlags::lemma_each_bit_is_valid;

    proof {
        bit_u32_and_auto();
        bit_u64_and_auto();
    }

    let inner = paddr.0;
    let huge_page = (inner & 0x3) == 1;
    let validate = (inner & 0x4) == 4;
    let guest_pa = inner & !(PAGE_SIZE as u64 - 1);
    let (len, page_size) = if huge_page {
        (512, PAGE_SIZE_2M)
    } else {
        (1, PAGE_SIZE)
    };

    if huge_page {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Other(0x6)));
    }
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

    if core::hint::unlikely(!check_within_guest_mmap(PhysAddr(guest_pa))) {
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
            kdebug!("Guest pvalidate: pvalidate failed at gpa:", PhysAddr(guest_pa), "with return code:", r, " has_changed:", has_changed);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Other(r)));
        }
        if !has_changed {
            if inner & 0x8 == 0x8 {
                return Ok(());
            } else {
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
            if rmpadjust(
                temp_va.inner.start,
                page_size,
                RmpFlags::rwx_guest_vmpl1(),
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

#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
    ensures
        final(cpu_perm).wf(),
        final(cpu_perm).ptr_perm.value().cpu_id == old(cpu_perm).ptr_perm.value().cpu_id,
)]
pub(crate) fn handle_deko_service_pvalidate(params: &DekoGuestRequestParams) -> DekoGuestServResult<
    (),
> {
    if core::hint::unlikely(params.rcx % (core::mem::size_of::<u64>() as u64) != 0) {
        kerror!("Guest pvalidate: unaligned physical address: ", params.rcx);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if false {
        kerror!("Guest pvalidate: invalid physical address: ", params.rcx);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if core::hint::unlikely(params.rcx >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE) {
        kerror!("Guest pvalidate: physical address out of range: ", params.rcx);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let offset = params.rcx % PAGE_SIZE as u64;
    let guest_pa = PhysAddr(params.rcx & !(PAGE_SIZE as u64 - 1));

    if core::hint::unlikely(
        core::mem::size_of::<DekoGuestPValidateReq>() as u64 > PAGE_SIZE as u64 - offset,
    ) {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    proof {
        let guest_pa = guest_pa@;
        let rcx = params.rcx;
        assert(guest_pa % PAGE_SIZE == 0 && guest_pa <= rcx) by (bit_vector)
            requires
                guest_pa == (rcx & !((PAGE_SIZE as u64 - 1) as u64)),
                PAGE_SIZE == 0x1000,
        ;
    }

    let paddr_range = create_paddr_range(guest_pa, 1);
    let temp_mapping = TempMapping::new(paddr_range);

    if let Some(temp_va) = temp_mapping {
        let mut guest_req = read_guest_copied::<DekoGuestPValidateReq>(
            VirtAddr(temp_va.inner.start.0 + offset),
        );

        let entries = guest_req.entries;
        let next = guest_req.next;
        let max_entries = (PAGE_SIZE - offset - core::mem::size_of::<
            DekoGuestPValidateReq,
        >() as u64) / core::mem::size_of::<u64>() as u64;

        if entries == 0 || entries > max_entries as u16 || entries <= next {
            kerror!("Guest pvalidate: invalid request parameters: entries=", entries, " next=", next, " max_entries=", max_entries);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        if core::hint::unlikely(
            u64::MAX - entries as u64 * PAGE_SIZE <= temp_va.inner.start.0 + offset,
        ) {
            kerror!("Guest pvalidate: request size overflow: entries=", entries, " next=", next);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        let mut pvalidate_result = Ok(());
        let mut i = next;
        #[verus_spec(
            invariant_except_break
                guest_req.next == i,
                next <= i <= entries <= max_entries,
                temp_va.wf(),
                temp_va.inner.start@ + (entries * PAGE_SIZE) <= u64::MAX,
                entries as int >= 0,
                offset <= PAGE_SIZE,
                max_entries <= PAGE_SIZE,
                core::mem::size_of::<u64>() == 8,
                core::mem::size_of::<DekoGuestPValidateReq>() == 8,
                cpu_perm.wf(),
                PAGE_SIZE == 0x1000,
                cpu_perm.ptr_perm.value().cpu_id == old(cpu_perm).ptr_perm.value().cpu_id,
            ensures
                cpu_perm.wf(),
                cpu_perm.ptr_perm.value().cpu_id == old(cpu_perm).ptr_perm.value().cpu_id,
            decreases
                entries - i,
        )]
        while i < entries {
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
                Err(ref e) => match e {
                    DekoGuestServError::SoftError(_) => break ,
                    DekoGuestServError::FatalError(_) => return pvalidate_result,
                },
            };

            i += 1;
        }

        write_guest(VirtAddr(temp_va.inner.start.0 + offset), guest_req);

        pvalidate_result
    } else {
        kerror!("Guest pvalidate: failed to create temporary mapping for gpa: ", guest_pa.0);
        Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy))
    }
}

#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
        old(cpu_perm).ptr_perm.value().cpu_id == cpu_idx,
    ensures
        final(cpu_perm).wf(),
        final(cpu_perm).ptr_perm.value().cpu_id == cpu_idx,
)]
pub(crate) fn handle_deko_service_remap_ca(
    params: &mut DekoGuestRequestParams,
    cpu_idx: u64,
) -> DekoGuestServResult<()> {
    let ca_pa = params.rcx;

    if core::hint::unlikely(!valid_guest_page(PhysAddr(ca_pa))) {
        kerror!("Guest remap CA: invalid CA page: ca_pa=", ca_pa);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    let ca_mapping = match TempMapping::new(create_paddr_range(PhysAddr(ca_pa), 1)) {
        Some(m) => m,
        None => {
            kerror!("Guest remap CA: failed to create temporary mapping for CA page at: ", PhysAddr(ca_pa));
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
        },
    };

    ca_mapping.write_bytes(0, PAGE_SIZE as usize);

    deko_rwlock_read_atomic_data! {
        PERCPU_AREAS,
        percpu_areas,
        percpu_areas_perm,
        {
            crate::check_shared_cpu_idx!(cpu_idx as usize, percpu_areas, percpu_areas);
            let this_cpu = &percpu_areas.0[cpu_idx as usize];

            deko_rwlock_write_atomic_data! {
                this_cpu.guest_vmsa,
                guest_vmsa,
                __,
                {
                    guest_vmsa.caa = Some(PhysAddr(ca_pa));
                    guest_vmsa.generation = guest_vmsa.generation.wrapping_add(1);
                }
            }
        }
    }

    Ok(())
}

} // verus!
