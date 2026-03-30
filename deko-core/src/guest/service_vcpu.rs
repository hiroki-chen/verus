use core::sync::atomic::AtomicBool;

use deko_std::address::{create_paddr_range, PhysAddr};
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto};
use deko_std::mem::PAGE_SIZE;
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use deko_std::{deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data};
use vstd::prelude::*;

use crate::cpu::tlb::flush_tlb_global_sync;
use crate::cpu::{DekoCpuCtxPermission, PERCPU_AREAS};
use crate::guest::{
    valid_guest_page, DekoGuestRequestParams, DekoGuestServError, DekoGuestServResult,
    DekoGuestServResultCode,
};
use crate::imp::RmpFlags;
use crate::kerror;
use crate::mm::vm::TempMapping;
use crate::snp::rmpadjust;
use crate::snp::vmsa::VMSA;

verus! {

pub(crate) exec static RMP_GUARD: AtomicBool = AtomicBool::new(false);

#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
    ensures
        cpu_perm.wf(),
        cpu_perm.ptr_perm.value().cpu_id == old(cpu_perm).ptr_perm.value().cpu_id,
)]
pub(crate) fn handle_deko_service_vcpu_destroy(
    params: &DekoGuestRequestParams,
) -> DekoGuestServResult<()> {
    broadcast use RmpFlags::lemma_each_bit_is_valid;

    proof {
        bit_u32_and_auto();
        bit_u64_and_auto();
    }

    let vmsa = params.rcx;

    if core::hint::unlikely(!valid_guest_page(PhysAddr(vmsa))) {
        kerror!("Guest vCPU destroy: invalid vmsa page: vmsa=", vmsa);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    let pvmsa = PhysAddr(vmsa);
    let vmsa_mapping = match TempMapping::new(create_paddr_range(pvmsa, 1)) {
        Some(m) => m,
        None => {
            kerror!("Guest vCPU destroy: failed to create temporary mapping for VMSA page at: ", pvmsa);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
        },
    };

    assume(cpu_perm.pgtable_perm.mapped_region(vmsa_mapping.inner));

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
pub(crate) fn handle_deko_service_vcpu_create(
    params: &DekoGuestRequestParams,
) -> DekoGuestServResult<()> {
    broadcast use RmpFlags::lemma_each_bit_is_valid;

    proof {
        bit_u32_and_auto();
        bit_u64_and_auto();
    }

    let vcpu_id = params.r8 & 0xffff_ffff;
    let vmsa_page = params.rcx;
    let caa_page = params.rdx;
    let sev_features = params.sev_features;

    if core::hint::unlikely(
        !valid_guest_page(PhysAddr(vmsa_page)) || !valid_guest_page(PhysAddr(caa_page)),
    ) {
        kerror!("Guest vCPU create: invalid vmsa or caa page: vmsa=", vmsa_page, " caa=", caa_page);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    let pvmsa = PhysAddr(vmsa_page);
    let pcaa = PhysAddr(caa_page);

    let mut attempt = 0xffff_ffffu32;
    let mut ok = false;
    #[verus_spec(
        decreases
            attempt,
    )]
    while attempt != 0 {
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
            Err(_) => {},
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

    {
        proof {
            assume(core::mem::size_of::<VMSA>() == 4096);
        }

        let vmsa = vmsa_mapping.read_ref::<VMSA>();
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
        RmpFlags::from_bits_truncate(RmpFlags::vmpl2().bits()),
        Tracked(&mut cpu_perm.pgtable_perm),
    );

    flush_tlb_global_sync();

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
            if let Some(percpu_areas) = percpu_areas {
                if core::hint::unlikely(vcpu_id as usize >= percpu_areas.0.len()) {
                    kerror!("Guest vCPU create: invalid vCPU ID: ", vcpu_id);
                    Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                } else {
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

} // verus!
