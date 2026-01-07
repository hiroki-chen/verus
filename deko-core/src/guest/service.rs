use core::sync::atomic::AtomicBool;

use deko_macros::DekoDebug;
use deko_std::address::{create_paddr_range, PhysAddr, VirtAddr};
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto};
use deko_std::mem::{PAGE_SIZE, PAGE_SIZE_2M};
use deko_std::misc::early_dbg;
use deko_std::wf::WellFormed;
use deko_std::{deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data, trace_enable};
use vstd::prelude::*;

use crate::cpu::tlb::{flush_tlb_global_percpu, flush_tlb_global_sync};
use crate::cpu::{DekoCpuCtxPermission, PERCPU_AREAS};
use crate::guest::{
    DekoGuestRequestParams, DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode,
};
use crate::imp::RmpFlags;
use crate::mm::vm::TempMapping;
use crate::mm::zero_page;
use crate::snp::vmsa::VMSA;
use crate::snp::{pvalidate, rmpadjust, validate_vaddr_region};
use crate::{kdebug, kerror, kinfo, kwarn};

verus! {

exec static RMP_GUARD: AtomicBool = AtomicBool::new(false);

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
        cpu_perm.ptr_perm.value().cpu_id == old(cpu_perm).ptr_perm.value().cpu_id,
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
// #[verifier::external_body]
#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
    ensures
        cpu_perm.wf(),
        cpu_perm.ptr_perm.value().cpu_id == old(cpu_perm).ptr_perm.value().cpu_id,
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

    if core::hint::unlikely(
        offset + core::mem::size_of::<DekoGuestPValidateReq>() as u64 > PAGE_SIZE as u64,
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

    // Now we need to create a temporary mapping for the guest
    // physical address so that we can access the request structure.
    let paddr_range = create_paddr_range(guest_pa, 1);
    let temp_mapping = TempMapping::new(paddr_range);

    if let Some(temp_va) = temp_mapping {
        // SAFETY: We have verified that the guest_pa is valid
        // and the temporary mapping guarantees that we have
        // mapped the physical address on the current core.
        // todo: use temp_mapping read.
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

            i += 1;
        }

        // Write back to the guest request structure.
        write_guest(VirtAddr(temp_va.inner.start.0 + offset), guest_req);

        pvalidate_result
    } else {
        kerror!("Guest pvalidate: failed to create temporary mapping for gpa: ", guest_pa.0);

        Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy))
    }
}

/// The guest is requesting for vCPU destruction.
#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
    ensures
        cpu_perm.wf(),
        cpu_perm.ptr_perm.value().cpu_id == old(cpu_perm).ptr_perm.value().cpu_id,
)]
pub fn handle_deko_service_vcpu_destroy(params: &DekoGuestRequestParams) -> DekoGuestServResult<
    (),
> {
    broadcast use RmpFlags::lemma_each_bit_is_valid;

    proof {
        bit_u32_and_auto();
        bit_u64_and_auto();
    }

    let vmsa = params.rcx;

    if core::hint::unlikely(vmsa % PAGE_SIZE != 0) {
        kerror!("Guest vCPU destroy: unaligned vmsa page: vmsa=", vmsa);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    if false {  /* Check if this address falls within the guest physical address regions. */
        // Placeholder for now.
        kerror!("Guest vCPU destroy: invalid vmsa page: vmsa=", vmsa);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    if core::hint::unlikely(vmsa >= 0x000f_ffff_ffff_f000u64 - PAGE_SIZE) {
        kerror!("Guest vCPU destroy: vmsa page out of range: vmsa=", vmsa);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    // Map it temporarily.

    let pvmsa = PhysAddr(vmsa);
    let vmsa_mapping = match TempMapping::new(create_paddr_range(pvmsa, 1)) {
        Some(m) => m,
        None => {
            kerror!("Guest vCPU destroy: failed to create temporary mapping for VMSA page at: ", pvmsa);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
        },
    };

    assume(cpu_perm.pgtable_perm.mapped_region(vmsa_mapping.inner));

    // Now we adjust the RMP permissions.
    if rmpadjust(
        vmsa_mapping.inner.start,
        PAGE_SIZE,
        RmpFlags::rwx_guest_vmpl2(),
        Tracked(&mut cpu_perm.pgtable_perm),
    ) != 0 {
        kerror!("Guest vCPU destroy: failed to adjust RMP for VMSA page at: ", pvmsa);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidReq));
    }
    flush_tlb_global_sync();

    Ok(())
}

#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
    ensures
        cpu_perm.wf(),
        cpu_perm.ptr_perm.value().cpu_id == old(cpu_perm).ptr_perm.value().cpu_id,
)]
fn handle_deko_service_vcpu_create(params: &DekoGuestRequestParams) -> DekoGuestServResult<()> {
    broadcast use RmpFlags::lemma_each_bit_is_valid;

    proof {
        bit_u32_and_auto();
        bit_u64_and_auto();
    }

    // Extract the parameters.
    let vcpu_id = params.r8 & 0xffff_ffff;
    // the physical address of the vmsa page.
    let vmsa_page = params.rcx;
    // the physical address of the caa page.
    let caa_page = params.rdx;
    let sev_features = params.sev_features;

    // kinfo!(
    //     "Guest vCPU create: vcpu_id =", vcpu_id,
    //     "vmsa_page =", vmsa_page => hex,
    //     "caa_page =", caa_page => hex,
    //     "sev_features =", sev_features
    // );

    // Check the alignment of the pages.
    if core::hint::unlikely(vmsa_page % PAGE_SIZE != 0 || caa_page % PAGE_SIZE != 0) {
        kerror!("Guest vCPU create: unaligned vmsa or caa page: vmsa=", vmsa_page, " caa=", caa_page);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    if false {  /* Check if this address falls within the guest physical address regions. */
        // Placeholder for now.
        kerror!("Guest vCPU create: invalid vmsa or caa page: vmsa=", vmsa_page, " caa=", caa_page);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    if core::hint::unlikely(
        vmsa_page >= 0x000f_ffff_ffff_f000u64 - PAGE_SIZE || caa_page >= 0x000f_ffff_ffff_f000u64
            - PAGE_SIZE,
    ) {
        kerror!("Guest vCPU create: vmsa or caa page out of range: vmsa=", vmsa_page, " caa=", caa_page);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    let pvmsa = PhysAddr(vmsa_page);
    let pcaa = PhysAddr(caa_page);

    // Since vCPU creation requires page validation; we need to
    // acquire the RMP guard here.
    let mut attempt = 0xffff_ffffu32;
    let mut ok = false;
    #[verus_spec(
        decreases
            attempt,
    )]
    while attempt != 0 {
        // Try to acquire the RMP guard.
        match RMP_GUARD.compare_exchange_weak(
            false,
            true,
            core::sync::atomic::Ordering::Relaxed,
            core::sync::atomic::Ordering::Relaxed,
        ) {
            Ok(_) => {
                ok = true;
                break ;
            },
            Err(_) => {
                // Failed to acquire the guard; retry.
            },
        }
        attempt -= 1;
    }

    if !ok {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
    }
    let vmsa_mapping = match TempMapping::new(create_paddr_range(pvmsa, 1)) {
        Some(m) => m,
        None => {
            RMP_GUARD.store(false, core::sync::atomic::Ordering::Release);
            kerror!("Guest vCPU create: failed to create temporary mapping for VMSA page at: ", pvmsa);

            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
        },
    };

    // Perform a sanity check here.
    {
        proof {
            // TODO: We port size information to another module for
            // better organization and readability.
            assume(core::mem::size_of::<VMSA>() == 4096);
        }

        let vmsa = vmsa_mapping.read_ref::<VMSA>();
        // kinfo!("Guest vCPU create: VMSA read: ", vmsa);

        // Now check if the VMSA is valid.
        if vmsa.vmpl != 2 || vmsa.efer & (1 << 12) == 0 || vmsa.sev_features != sev_features {
            kerror!("Guest vCPU create: invalid VMSA parameters");

            RMP_GUARD.store(false, core::sync::atomic::Ordering::Release);

            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
    }

    assume(cpu_perm.pgtable_perm.mapped_region(vmsa_mapping.inner));

    rmpadjust(
        vmsa_mapping.inner.start,
        PAGE_SIZE,
        RmpFlags::from_bits_truncate(RmpFlags::vmpl3().bits()),
        Tracked(&mut cpu_perm.pgtable_perm),
    );

    flush_tlb_global_sync();

    // Now adjust the permission.
    if rmpadjust(
        vmsa_mapping.inner.start,
        PAGE_SIZE,
        RmpFlags::from_bits_truncate(RmpFlags::vmsa().bits() | RmpFlags::vmpl2().bits()),
        Tracked(&mut cpu_perm.pgtable_perm),
    ) != 0 {
        RMP_GUARD.store(false, core::sync::atomic::Ordering::Release);

        kerror!("Guest vCPU create: failed to adjust RMP for VMSA page at: ", pvmsa);

        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidReq));
    }
    RMP_GUARD.store(false, core::sync::atomic::Ordering::Release);

    deko_rwlock_read_atomic_data! {
        PERCPU_AREAS,
        percpu_areas,
        percpu_areas_perm,
        {
            // crate::check_shared_cpu_idx!(vcpu_id as usize, percpu_areas, percpu_areas);
            if let Some(percpu_areas) = percpu_areas {
                if core::hint::unlikely(vcpu_id as usize >= percpu_areas.0.len()) {
                    kerror!("Guest vCPU create: invalid vCPU ID: ", vcpu_id);
                    Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                } else {
                    // Fetch the per-CPU area.
                    let this_cpu = &percpu_areas.0[vcpu_id as usize];
                    let guest_vmsa = &this_cpu.guest_vmsa;

                    deko_rwlock_write_atomic_data! {
                        guest_vmsa,
                        guest_vmsa_ref,
                        __,
                        {
                            guest_vmsa_ref.caa.replace(pcaa);
                            guest_vmsa_ref.vmsa.replace(pvmsa);
                            guest_vmsa_ref.generation = guest_vmsa_ref.generation.wrapping_add(1);
                        }
                    }

                    Ok(())
                }
            } else {
                kerror!("Guest vCPU create: internal error");
                Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy))
            }
        }
    }?;

    Ok(())
}

/// The SVSM calling area (CA) is used to communicate between the Linux
/// and the SVSM. Since the firmware supplied CA for the BSP is likely
/// to be in reserved memory, switch off that CA to a kernel provided
/// CA is done using the SVSM core protocol call.
#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
        old(cpu_perm).ptr_perm.value().cpu_id == cpu_idx,
    ensures
        cpu_perm.wf(),
        cpu_perm.ptr_perm.value().cpu_id == cpu_idx,
)]
fn handle_deko_service_remap_ca(
    params: &mut DekoGuestRequestParams,
    cpu_idx: u64,
) -> DekoGuestServResult<()> {
    // static void __init svsm_setup(struct cc_blob_sev_info *cc_info)
    let ca_pa = params.rcx;

    if core::hint::unlikely(ca_pa % PAGE_SIZE != 0) {
        kerror!("Guest remap CA: unaligned CA page: ca_pa=", ca_pa);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    if false {  /* Check if this address falls within the guest physical address regions. */
        // Placeholder for now.
        kerror!("Guest remap CA: invalid CA page: ca_pa=", ca_pa);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    if core::hint::unlikely(ca_pa >= 0x000f_ffff_ffff_f000u64 - PAGE_SIZE) {
        kerror!("Guest remap CA: ca page out of range: ca_pa=", ca_pa);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    let ca_mapping = match TempMapping::new(create_paddr_range(PhysAddr(ca_pa), 1)) {
        Some(m) => m,
        None => {
            kerror!("Guest remap CA: failed to create temporary mapping for CA page at: ", PhysAddr(ca_pa));

            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
        },
    };

    // Clear it.
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

/// Subroutine for handling DEKO service requests from the guest.
///
/// Note during process handling there would be lock held so obtaining
/// the cpu permission is necessary.
#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
        old(cpu_perm).ptr_perm.value().cpu_id == cpu_idx,
    ensures
        cpu_perm.wf(),
        cpu_perm.ptr_perm.value().cpu_id == cpu_idx,
)]
pub(super) fn handle_guest_exit_deko_service(
    req: u32,
    params: &mut DekoGuestRequestParams,
    cpu_idx: u64,
) -> DekoGuestServResult<()> {
    match req {
        DEKO_SERVICE_REMAP_CA => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_remap_ca(params, cpu_idx)
        },
        DEKO_SERVICE_PVALIDATE => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_pvalidate(params)
        },
        DEKO_SERVICE_CREATE_VCPU => {
            trace_enable(true);
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_vcpu_create(params)
        },
        DEKO_SERVICE_DESTROY_VCPU => {
            trace_enable(false);

            proof_with!(Tracked(cpu_perm));
            handle_deko_service_vcpu_destroy(params)
        },
        _ => {
            kerror!("Unsupported deko service request: ", req);
            Err(DekoGuestServError::SoftError(DekoGuestServResultCode::UnsupportedProtocol))
        },
    }
}

} // verus!
