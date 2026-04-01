use deko_macros::with_atomic_pred;
use deko_std::address::{PhysAddr, VirtAddr};
use deko_std::mem::{PAGE_SIZE, PAGE_SIZE_2M};
use deko_std::misc::early_dbg;
use deko_std::sync::{DekoOnceCell, DekoSimpleOnceCell};
use deko_std::wf::WellFormed;
use deko_std::{trace_enable, TrivialPredicate};
use vstd::prelude::*;

use crate::cpu::task::try_enter_guest;
use crate::cpu::tlb::flush_tlb_global_percpu;
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::guest::service_extend::handle_guest_exit_extend_service;
use crate::guest::{
    DekoGuestRequestParams, DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode,
    DEKO_SERVICE_ATTEST_SERVICES, DEKO_SERVICE_ATTEST_SINGLE_SERVICE, DEKO_SERVICE_CREATE_VCPU,
    DEKO_SERVICE_DESTROY_VCPU, DEKO_SERVICE_PVALIDATE, DEKO_SERVICE_REMAP_CA,
};
use crate::snp::vmsa::VMSA;
use crate::{kerror, kunimplemented};

verus! {

with_atomic_pred! {
    PhysAddr,
    (),
    fields: {},
    perm_fields: {},
    data.view() % PAGE_SIZE == 0 && data.view() < 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE_2M
}

pub(crate) exec static TRAMPOLINE_PA: DekoOnceCell<PhysAddr, (), PhysAddrPred>
    ensures
        TRAMPOLINE_PA.wf(),
{
    DekoOnceCell::new(Ghost(PhysAddrPred {  }))
}

/// Reads a reference to type `T` from the given guest virtual address.
#[inline(always)]
#[verifier::external_body]
#[verus_spec(r =>
    requires
        // ?
)]
pub(super) fn read_guest_copied<T: Copy>(addr: VirtAddr) -> T {
    unsafe { core::ptr::read_unaligned(addr.0 as *const T) }
}

#[inline(always)]
#[verifier::external_body]
#[verus_spec(r =>
    requires
        // ?
)]
pub(super) fn write_guest<T>(addr: VirtAddr, val: T) {
    unsafe {
        core::ptr::write_unaligned(addr.0 as *mut T, val);
    }
}

/// Subroutine for handling DEKO service requests from the guest.
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
pub(super) fn handle_guest_exit_deko_service(
    req: u32,
    params: &mut DekoGuestRequestParams,
    cpu_idx: u64,
) -> DekoGuestServResult<()> {
    match req {
        DEKO_SERVICE_REMAP_CA => {
            proof_with!(Tracked(cpu_perm));
            crate::guest::service_memory::handle_deko_service_remap_ca(params, cpu_idx)
        },
        DEKO_SERVICE_PVALIDATE => {
            proof_with!(Tracked(cpu_perm));
            crate::guest::service_memory::handle_deko_service_pvalidate(params)
        },
        DEKO_SERVICE_CREATE_VCPU => {
            trace_enable(true);
            proof_with!(Tracked(cpu_perm));
            crate::guest::service_vcpu::handle_deko_service_vcpu_create(params)
        },
        DEKO_SERVICE_DESTROY_VCPU => {
            trace_enable(false);
            proof_with!(Tracked(cpu_perm));
            crate::guest::service_vcpu::handle_deko_service_vcpu_destroy(params)
        },
        _ => {
            kerror!("Unsupported deko service request: ", req);
            VMSA::err_dump_vmsa();

            Err(DekoGuestServError::SoftError(DekoGuestServResultCode::UnsupportedProtocol))
        },
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
pub(super) fn handle_guest_exit_attest_service(
    req: u32,
    params: &mut DekoGuestRequestParams,
    cpu_idx: u64,
) -> DekoGuestServResult<()> {
    match req {
        DEKO_SERVICE_ATTEST_SERVICES => { kunimplemented!() },
        DEKO_SERVICE_ATTEST_SINGLE_SERVICE => { kunimplemented!() },
        _ => {
            kerror!("Unsupported attestation service request: ", req);
            Err(DekoGuestServError::SoftError(DekoGuestServResultCode::UnsupportedProtocol))
        },
    }
}

} // verus!
