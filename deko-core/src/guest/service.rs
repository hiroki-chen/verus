use core::sync::atomic::AtomicBool;

use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::address::{create_paddr_range, PhysAddr, VirtAddr};
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto, lemma_aligned_to_4k};
use deko_std::mem::{PAGE_SIZE, PAGE_SIZE_2M, PERCPU_BASE, PERCPU_END};
use deko_std::misc::early_dbg;
use deko_std::prelude::VADDR_UPPER_MASK;
use deko_std::ptr::DekoPPtr;
use deko_std::sync::{DekoAtomicData, DekoOnceCell, DekoSimpleOnceCell};
use deko_std::wf::WellFormed;
use deko_std::{
    deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data, trace_enable, TrivialPredicate,
};
use vstd::prelude::*;

use crate::cpu::irq::no_irq_zone;
use crate::cpu::regs::MSR_LSTAR;
use crate::cpu::task::try_enter_guest;
use crate::cpu::tlb::{flush_tlb_global_percpu, flush_tlb_global_sync};
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission, PERCPU_AREAS};
use crate::guest::{
    self, guest_page_table, DekoGuestRequestParams, DekoGuestServError, DekoGuestServResult,
    DekoGuestServResultCode, PtRegs, DEKO_POLICY_ENGINE_BLOB,
};
use crate::imp::RmpFlags;
use crate::mm::paging::{
    self, make_shared_address, strip_confidentiality_bits, PageTable, PageTableEntry, PageTablePath,
};
use crate::mm::vm::TempMapping;
use crate::mm::{check_within_guest_mmap, virt_to_phys, zero_page};
use crate::policy::guest_paging::{GuestPageOffsetBase, GUEST_PAGE_OFFSET_BASE};
use crate::policy::syscall::{analyze_and_prepare_syscall, SYS_exit, SYS_exit_group};
use crate::policy::userapp::{register_user_app, try_kick_app};
use crate::policy::{
    self, deko_sysret_trampoline_func_ptr, deko_trampoline_start_func_ptr, enable_syscall_hook,
    inject_ifc_policy_engine, install_hook, DekoMsrIntercept, DekoMsrInterceptVec0,
    DekoSyscallBody,
};
use crate::snp::ghcb::vmpl_switch;
use crate::snp::vmsa::VMSA;
use crate::snp::{pvalidate, rmpadjust, validate_vaddr_region, VMPL_GUEST_KERNEL};
use crate::{kdebug, kerror, kinfo, kpanic_if, kunimplemented, kwarn, SELF_MAP};

const _: () = {
    assert!(core::mem::size_of::<DekoGuestLstarWriteReq>() == 0x30);
    assert!(core::mem::size_of::<DekoNewAppReq>() == 0x60);
};

verus! {

exec static RMP_GUARD: AtomicBool = AtomicBool::new(false);

global layout DekoGuestPValidateReq is size == 8;

global layout DekoGuestLstarWriteReq is size == 0x30;

global layout DekoNewAppReq is size == 0x60;

global layout DekoMapIfcReq is size == 0x290;

pub const DEKO_SERVICE_APP_ENTER_OK: u64 = 0x9000_0000;

pub const DEKO_SERVICE_APP_EXIT: u64 = 0x9000_0001;

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

/// Represents a request structure for LSTAR MSR write operations.
/// The guest must place this request at the given physical address
/// before invoking the LSTAR write service.
#[repr(C, align(8))]
#[derive(Copy, Clone, DekoDebug)]
pub struct DekoGuestLstarWriteReq {
    /// The guest virtual address of the syscall entry point.
    pub syscall_enter_addr: VirtAddr,
    /// The guest allocated virtual address of the trampoline area.
    pub trampoline_gva: VirtAddr,
    /// The physical address of the trampoline code.
    pub trampoline_gpa: PhysAddr,
    /// The physical address of the IFC policy engine blob.
    pub blob_gpa: PhysAddr,
    /// Guest  page offset base.
    pub page_offset_base: VirtAddr,
    /// Being returned.
    pub sysret_trampoline: u64,
}

#[repr(C, align(8))]
#[derive(Copy, Clone, DekoDebug)]
pub struct DekoMapIfcSingleReq {
    #[deko(hex)]
    pub va_start: u64,
    #[deko(hex)]
    pub va_end: u64,
    #[deko(hex)]
    pub pa_start: u64,
    #[deko(hex)]
    pub pa_end: u64,
    pub is_percpu: u64,
}

#[repr(C, align(8))]
#[derive(Copy, Clone, DekoDebug)]
pub struct DekoMapIfcReq {
    pub req_len: u16,
    pub _reserved: [u16; 3],
    pub ghcb_va: u64,
    pub reqs: [DekoMapIfcSingleReq; 16],
}

#[allow(non_camel_case_types)]
#[repr(u32)]
#[derive(Copy, Clone, DekoDebug, PartialEq, Eq)]
pub enum DekoNewAppType {
    DEKO_DOCKER_INFRA = 0,
    DEKO_DOCKER_APPS = 1,
    DEKO_UNKNOWN = 0xffffffff,
}

#[repr(C, align(8))]
#[derive(Copy, Clone, DekoDebug)]
pub struct DekoNewAppReq {
    /// Process ID (current->pid)
    pub pid: u32,
    /// Thread Group ID (current->tgid).
    /// Used to identify the main thread.
    pub tgid: u32,
    /// Parent PID (current->real_parent->pid).
    /// Essential for building the process tree.
    pub ppid: u32,
    /// User ID (current_cred()->uid).
    /// Used for privilege checks (root vs non-root).
    pub uid: u32,
    /// Pointer or ID of the Mount Namespace.
    /// (u64)current->nsproxy->mnt_ns
    /// If two processes share this, they are in the same container filesystem view.
    pub mnt_ns_id: u64,
    /// The start code virtual address of the new application.
    pub start_code: u64,
    /// The end code virtual address of the new application.
    pub end_code: u64,
    /// The beginning of the user stack.
    pub user_stack: u64,
    /// The size of the user stack.
    pub user_stack_size: u64,
    /// Command excluding the path.
    pub comm: [u8; 16],
    pub token_low: u64,
    pub token_high: u64,
    pub app_type: DekoNewAppType,
}

impl WellFormed for DekoNewAppReq {
    open spec fn wf(&self) -> bool {
        true
    }
}

pub const DEKO_SERVICE_REMAP_CA: u32 = 0x0;

pub const DEKO_SERVICE_PVALIDATE: u32 = 0x1;

pub const DEKO_SERVICE_CREATE_VCPU: u32 = 0x2;

pub const DEKO_SERVICE_DESTROY_VCPU: u32 = 0x3;

pub const DEKO_SERVICE_DEPOSIT_MEMORY: u32 = 0x4;

pub const DEKO_SERVICE_WITHDRAW_MEMORY: u32 = 0x5;

pub const DEKO_SERVICE_QUERY_PROTOCOL: u32 = 0x6;

pub const DEKO_SERVICE_ATTEST_SERVICES: u32 = 0x0;

pub const DEKO_SERVICE_ATTEST_SINGLE_SERVICE: u32 = 0x1;

pub const DEKO_SERVICE_EXTEND_MSR_INTERCEPT: u32 = 0x0;

pub const DEKO_SERVICE_EXTEND_SYSCALL_ANALYSIS: u32 = 0x1;

pub const DEKO_SERVICE_EXTEND_REPORT_APP: u32 = 0x2;

pub const DEKO_SERVICE_EXTEND_LAUNCH_APP: u32 = 0x3;

pub const DEKO_SERVICE_EXTEND_MAP_IFC: u32 = 0x4;

pub const DEKO_SERVICE_EXTEND_INVOKE_UNTRUSTED_SYSCALL_HANDLER: u32 = 0x5;

with_atomic_pred! {
    PhysAddr,
    (),
    fields: {},
    perm_fields: {},
    data.view() % PAGE_SIZE == 0 && data.view() < 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE_2M
}

exec static TRAMPOLINE_PA: DekoOnceCell<PhysAddr, (), PhysAddrPred>
    ensures
        TRAMPOLINE_PA.wf(),
{
    DekoOnceCell::new(Ghost(PhysAddrPred {  }))
}

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

    // HACK: For now we do not support huge page validation.
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

    // Need to first check if the physical address is
    // within the expected guest physical regions.
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
            if rmpadjust(
                temp_va.inner.start,
                page_size,
                RmpFlags::rwx_guest_vmpl1(),  // also make it accessible to VMPL1.
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
    if core::hint::unlikely(!check_within_guest_mmap(PhysAddr(vmsa))) {
        // Check if this address falls within the guest physical address regions.
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

    // Check the alignment of the pages.
    if core::hint::unlikely(vmsa_page % PAGE_SIZE != 0 || caa_page % PAGE_SIZE != 0) {
        kerror!("Guest vCPU create: unaligned vmsa or caa page: vmsa=", vmsa_page, " caa=", caa_page);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    if core::hint::unlikely(!check_within_guest_mmap(PhysAddr(vmsa_page))) {
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
        RmpFlags::from_bits_truncate(RmpFlags::vmpl2().bits()),
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

                    handle_deko_service_vcpu_create_syscall_intercept(vmsa_mapping)
                }
            } else {
                kerror!("Guest vCPU create: internal error");
                Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy))
            }
        }
    }?;

    Ok(())
}

/// Also enable the syscall intercept for the newly created vCPU.
#[inline]
#[verifier::external_body]
#[verus_spec(
    requires
        vmsa_mapping.wf(),
)]
fn handle_deko_service_vcpu_create_syscall_intercept(
    vmsa_mapping: TempMapping,
) -> DekoGuestServResult<()> {
    let ptr = vmsa_mapping.inner.start.0;
    let ptr = DekoPPtr(vstd::simple_pptr::PPtr(ptr as usize, core::marker::PhantomData));

    proof_with!(Tracked::assume_new());
    VMSA::enable_msr_intercept(
        ptr,
        &[DekoMsrIntercept::InterceptMsrVec0(DekoMsrInterceptVec0::LstarWrite)],
    );

    Ok(())
}

/// The SVSM calling area (CA) is used to communicate between the Linux
/// and the SVSM. Since the firmware supplied CA for the BSP is likely
/// to be in reserved memory, switch off that CA to a kernel provided
/// CA is done using the SVSM core protocol call.
///
/// This call is used to request that a new gPA be used for all future
/// communication with the SVSM. If should replace the affected vCPU's
/// caa field in its VMSA structure and a new mapping should be created.
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
    if core::hint::unlikely(!check_within_guest_mmap(PhysAddr(ca_pa))) {
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

/// Handles lstar interception.
///
/// RCX => MSR index (MSR_LSTAR)
/// RDX => Is write?
/// R9  => paddr of the request struct.
///
#[verus_spec(r =>

)]
fn handle_deko_service_lstar_intercept(
    params: &mut DekoGuestRequestParams,
    is_write: bool,
    guest_cr3: u64,
) -> DekoGuestServResult<()> {
    if is_write {
        // Fetch the request struct.
        let aligned_req = params.r9 & !(PAGE_SIZE as u64 - 1);
        let offset = params.r9 % PAGE_SIZE as u64;

        proof {
            let n = params.r9;

            assert(aligned_req % PAGE_SIZE == 0) by (bit_vector)
                requires
                    aligned_req == (n & !((PAGE_SIZE as u64 - 1) as u64)),
                    PAGE_SIZE == 0x1000,
            ;
        }

        if core::hint::unlikely(!check_within_guest_mmap(PhysAddr(aligned_req))) {
            kerror!("MSR intercept: LSTAR request struct NOT within guest mmap:", PhysAddr(params.r9));
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        if core::hint::unlikely(aligned_req >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE) {
            kerror!("MSR intercept: LSTAR request struct out of range:", PhysAddr(params.r9));
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        let lstar_req_mapping = match TempMapping::new(
            create_paddr_range(PhysAddr(aligned_req), 1),
        ) {
            Some(m) => m,
            None => {
                kerror!("MSR intercept: failed to create temporary mapping for LSTAR request struct at:", PhysAddr(params.r9));
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
            },
        };

        if core::hint::unlikely(
            offset + core::mem::size_of::<DekoGuestLstarWriteReq>() as u64 > PAGE_SIZE as u64,
        ) {
            kerror!("MSR intercept: LSTAR request struct exceeds page boundary:", PhysAddr(params.r9));
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        let req = lstar_req_mapping.read_ref_at::<DekoGuestLstarWriteReq>(offset as usize);
        let mut req = req.clone();
        let syscall_enter_addr = req.syscall_enter_addr.0;

        if req.page_offset_base.0 % PAGE_SIZE as u64 != 0 || req.page_offset_base.0
            < VADDR_UPPER_MASK {
            kerror!("MSR intercept: invalid page offset base:", req.page_offset_base => hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        if req.trampoline_gpa.0 % PAGE_SIZE as u64 != 0 {
            kerror!("MSR intercept: invalid trampoline gpa:", req.trampoline_gpa => hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        if req.trampoline_gpa.0 >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE_2M {
            kerror!("MSR intercept: trampoline gpa out of range:", req.trampoline_gpa => hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        if core::hint::unlikely(syscall_enter_addr < VADDR_UPPER_MASK) {
            kerror!("MSR intercept: invalid syscall enter address:", syscall_enter_addr => hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        kinfo!("Request:", req);

        let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
        let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
        let guest_cr3 = strip_confidentiality_bits(guest_cr3, cpu_borrow.private_bit);

        // First we need to perform a sanity check to ensure that
        // the guest CR3 is valid within the guest mmap.
        if !check_within_guest_mmap(PhysAddr(guest_cr3)) {
            kerror!("MSR intercept: guest CR3 NOT within guest mmap:", guest_cr3);
            kerror!("MSR intercept: cannot handle LSTAR MSR intercept without valid guest CR3");
            kerror!("MSR intercept: this is a serious security issue; aborting");

            return Err(DekoGuestServError::FatalError);
        }
        // Some alignment and range checks.

        if core::hint::unlikely(guest_cr3 % PAGE_SIZE != 0) {
            kerror!("MSR intercept: unaligned guest CR3:", guest_cr3);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        if core::hint::unlikely(guest_cr3 >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE) {
            kerror!("MSR intercept: guest CR3 out of range:", guest_cr3);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        let guest_pgtable = guest_page_table(guest_cr3)?;
        let syscall_enter_addr = VirtAddr(syscall_enter_addr);
        policy::install_hook(
            guest_pgtable,
            syscall_enter_addr,
            cpu_borrow.private_bit,
            cpu_borrow.shared_bit,
            &req,
        )?;

        if let Some(blob) = DEKO_POLICY_ENGINE_BLOB.get() {
            if req.trampoline_gva.0 % PAGE_SIZE as u64 != 0 {
                kerror!("MSR intercept: invalid trampoline gva for policy engine injection:", req.trampoline_gva => hex);
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
            }
            if req.trampoline_gva.0 <= VADDR_UPPER_MASK {
                kerror!("MSR intercept: trampoline gva for policy engine injection not in kernel space:", req.trampoline_gva => hex);
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
            }
        }
        req.sysret_trampoline = deko_sysret_trampoline_func_ptr().wrapping_sub(
            deko_trampoline_start_func_ptr(),
        );
        lstar_req_mapping.write_ref_at::<DekoGuestLstarWriteReq>(offset as usize, &req);

        kinfo!("MSR intercept: LSTAR MSR intercept handled successfully");

        if TRAMPOLINE_PA.get().is_none() {
            TRAMPOLINE_PA.init(DekoAtomicData::new(req.trampoline_gpa));
        }
    }
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
fn handle_deko_service_map_ifc(params: &mut DekoGuestRequestParams) -> DekoGuestServResult<()> {
    let gpa = params.rcx & !(PAGE_SIZE as u64 - 1);
    let offset = params.rcx % PAGE_SIZE as u64;

    proof {
        let n = params.rcx;

        assert(gpa % PAGE_SIZE == 0) by (bit_vector)
            requires
                gpa == (n & !((PAGE_SIZE as u64 - 1) as u64)),
                PAGE_SIZE == 0x1000,
        ;
    }

    let gpa = PhysAddr(gpa);

    if core::hint::unlikely(
        gpa.0 >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE || offset + core::mem::size_of::<
            DekoMapIfcReq,
        >() as u64 > PAGE_SIZE as u64,
    ) {
        kerror!("Map IFC: unaligned GPA: gpa=", gpa);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    if core::hint::unlikely(!check_within_guest_mmap(gpa)) {
        kerror!("Map IFC: invalid GPA: gpa=", gpa);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    let temp_mapping = match TempMapping::new(create_paddr_range(gpa, 1)) {
        Some(m) => m,
        None => {
            kerror!("Map IFC: failed to create temporary mapping for GPA at: ", gpa);

            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
        },
    };

    let mut req = temp_mapping.read_ref_at::<DekoMapIfcReq>(offset as _).clone();
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let private_bit = cpu_borrow.private_bit;
    let shared_bit = cpu_borrow.shared_bit;

    let sm = match SELF_MAP.get() {
        Some(sm) => sm,
        None => {
            kerror!("Map IFC: failed to get self-map regions");
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
        },
    };
    if sm.len() > 15 {
        kerror!("Map IFC: too many self-mapped regions: len=", sm.len());
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    for i in 0..sm.len()
        invariant
            sm.len() <= 15,
    {
        let this = DekoMapIfcSingleReq {
            va_start: sm[i].0.start.0,
            va_end: sm[i].0.end.0,
            pa_start: sm[i].1.start.0,
            pa_end: sm[i].1.end.0,
            is_percpu: 0,
        };

        req.reqs[i] = this;
    }

    req.req_len = (sm.len() + 1) as u16;
    // The last one is the percpu mapping.
    let paddr_percpu = virt_to_phys(
        private_bit,
        shared_bit,
        PERCPU_BASE,
        Tracked(&cpu_perm.pgtable_perm),
    ).0;
    req.reqs[sm.len() as usize] = DekoMapIfcSingleReq {
        va_start: PERCPU_BASE.0,
        va_end: PERCPU_BASE.0 + PAGE_SIZE,
        pa_start: paddr_percpu,
        pa_end: paddr_percpu.wrapping_add(PAGE_SIZE),
        is_percpu: 1,
    };

    let ghcb_va = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).ext_vmpl1.as_ref().ok_or(
        DekoGuestServError::SoftError(DekoGuestServResultCode::Busy),
    )?.ghcb.into_vaddr();

    req.ghcb_va = ghcb_va.0;
    temp_mapping.write_ref_at::<DekoMapIfcReq>(offset as _, &req);

    Ok(())
}

/// This function gets called by the guest to notify us that a new sensitive application
/// might have been launched so that we can register it accordingly.
///
/// The guest kernel replaces ctxt->ip to trampoline which does a VMMCALL which is intercepted
/// by us in the VMSA. The guest #VC handler then simply forwards the request to this function.
#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
        old(params).additional_data is Some,
    ensures
        cpu_perm.wf(),
        cpu_perm.ptr_perm.value().cpu_id == old(cpu_perm).ptr_perm.value().cpu_id,
)]
fn handle_deko_service_launch_app(params: &mut DekoGuestRequestParams) -> DekoGuestServResult<()> {
    let r9 = params.r9;
    let r9_offset = r9 % PAGE_SIZE as u64;
    let req_body = r9 & !0xfff;

    broadcast use lemma_aligned_to_4k;

    if core::hint::unlikely(!check_within_guest_mmap(PhysAddr(req_body))) {
        kerror!("Launch app: request body NOT within guest mmap:", PhysAddr(req_body));
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if core::hint::unlikely(
        req_body >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE || core::mem::size_of::<PtRegs>() as u64
            > PAGE_SIZE - r9_offset,
    ) {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let regs_mapping = TempMapping::new(create_paddr_range(PhysAddr(req_body), 1)).ok_or(
        DekoGuestServError::SoftError(DekoGuestServResultCode::Busy),
    )?;
    let regs = regs_mapping.read_ref_at::<PtRegs>(r9_offset as usize);

    try_kick_app(
        regs,
        PhysAddr(params.additional_data.unwrap().guest_cr3),
        (params.rdx & 0xffff_ffffu64) as u32,
        VirtAddr(params.rcx),
    )
}

#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
        old(params).additional_data is Some,
    ensures
        cpu_perm.wf(),
        cpu_perm.ptr_perm.value().cpu_id == old(cpu_perm).ptr_perm.value().cpu_id,
)]
fn handle_deko_service_report_app(params: &mut DekoGuestRequestParams) -> DekoGuestServResult<()> {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let private_bit = cpu_borrow.private_bit;
    let req_body = params.r9;
    let is_creation = params.r8 != 0;

    // Check if the request body is valid.
    if core::hint::unlikely(!check_within_guest_mmap(PhysAddr(req_body))) {
        kerror!("Report app: request body NOT within guest mmap:", PhysAddr(req_body));
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let offset = req_body % PAGE_SIZE as u64;
    let req_body = req_body & !0xfff;

    if core::hint::unlikely(
        req_body >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE || offset + core::mem::size_of::<
            DekoNewAppReq,
        >() as u64 > PAGE_SIZE as u64,
    ) {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    proof {
        let n = params.r9;

        assert(req_body % PAGE_SIZE == 0) by (bit_vector)
            requires
                req_body == (n & !((PAGE_SIZE as u64 - 1) as u64)),
                PAGE_SIZE == 0x1000,
        ;
    }

    let req_mapping = match TempMapping::new(create_paddr_range(PhysAddr(req_body), 1)) {
        Some(m) => m,
        None => {
            kerror!("Report app: failed to create temporary mapping for request body at:", PhysAddr(req_body));
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
        },
    };

    let mut req = req_mapping.read_ref_at::<DekoNewAppReq>(offset as usize).clone();
    let guest_cr3 = strip_confidentiality_bits(
        params.additional_data.unwrap().guest_cr3,
        private_bit,
    );

    register_user_app(&mut req, PhysAddr(guest_cr3), is_creation)?;
    req_mapping.write_ref_at::<DekoNewAppReq>(offset as usize, &req);

    Ok(())
}

#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
        old(params).additional_data is Some,
    ensures
        cpu_perm.wf(),
        cpu_perm.ptr_perm.value().cpu_id == old(cpu_perm).ptr_perm.value().cpu_id,
)]
fn handle_deko_service_msr_intercepts(params: &mut DekoGuestRequestParams) -> DekoGuestServResult<
    (),
> {
    let is_write = params.rdx != 0;

    if (params.rcx >= u32::MAX as u64) {
        kerror!("MSR intercept: invalid MSR index:", params.rcx);

        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    // params.rcx == MSR_INDEX.

    match (params.rcx as u32) {
        MSR_LSTAR => {
            let cr3 = params.additional_data.unwrap().guest_cr3;

            handle_deko_service_lstar_intercept(params, is_write, cr3)
        },
        msr => {
            kerror!("MSR intercept: unsupported MSR index:", msr);

            Err(DekoGuestServError::SoftError(DekoGuestServResultCode::UnsupportedProtocol))
        },
    }
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
        cpu_perm.wf(),
        cpu_perm.ptr_perm.value().cpu_id == cpu_idx,
)]
pub(super) fn handle_guest_exit_attest_service(
    req: u32,
    params: &mut DekoGuestRequestParams,
    cpu_idx: u64,
) -> DekoGuestServResult<()> {
    match req {
        DEKO_SERVICE_ATTEST_SERVICES => {
            // Handle attestation of all services.
            kunimplemented!()
        },
        DEKO_SERVICE_ATTEST_SINGLE_SERVICE => {
            // Handle attestation of a single service.
            kunimplemented!()
        },
        _ => {
            kerror!("Unsupported attestation service request: ", req);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::UnsupportedProtocol));
        },
    }
}

#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
        old(cpu_perm).ptr_perm.value().cpu_id == cpu_idx,
        old(params).additional_data is Some,
    ensures
        cpu_perm.wf(),
        cpu_perm.ptr_perm.value().cpu_id == cpu_idx,
)]
pub(super) fn handle_guest_exit_extend_service(
    req: u32,
    params: &mut DekoGuestRequestParams,
    cpu_idx: u64,
) -> DekoGuestServResult<()> {
    match req {
        DEKO_SERVICE_EXTEND_MSR_INTERCEPT => {
            kdebug!("MSR intercept:", params);

            proof_with!(Tracked(cpu_perm));
            handle_deko_service_msr_intercepts(params)
        },
        DEKO_SERVICE_EXTEND_REPORT_APP => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_report_app(params)
        },
        DEKO_SERVICE_EXTEND_LAUNCH_APP => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_launch_app(params)
        },
        DEKO_SERVICE_EXTEND_MAP_IFC => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_map_ifc(params)
        },
        _ => {
            kerror!("Unsupported extend service request: ", req);

            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::UnsupportedProtocol));
        },
    }
}

} // verus!
