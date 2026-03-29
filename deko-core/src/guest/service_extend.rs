use deko_std::address::{create_paddr_range, PhysAddr, VirtAddr};
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto, lemma_aligned_to_4k};
use deko_std::deko_rwlock_read_atomic_data;
use deko_std::mem::{PAGE_SIZE, PERCPU_BASE};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::collections::Vec;
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission, PERCPU_AREAS};
use crate::guest::{
    bind_current_cpu_vmpl1_slot, stage_fake_vmpl1_handoff_request, DekoGuestRequestParams,
    DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode, DekoLoadPolicyReq,
    DekoMapIfcReq, DekoMapIfcSingleReq, DekoNewAppReq, DekoTaskMigrateReq, PtRegs,
    DEKO_SERVICE_EXTEND_INVOKE_UNTRUSTED_SYSCALL_HANDLER, DEKO_SERVICE_EXTEND_LAUNCH_APP,
    DEKO_SERVICE_EXTEND_LOAD_POLICY, DEKO_SERVICE_EXTEND_MAP_IFC, DEKO_SERVICE_EXTEND_REPORT_APP,
    DEKO_SERVICE_EXTEND_TASK_MIGRATE, DEKO_SERVICE_EXTEND_TIMER_EVENT, DEKO_SERVICE_TIMER,
};
use crate::mm::frame_allocator::DekoAllocatorApi;
use crate::mm::paging::strip_confidentiality_bits;
use crate::mm::vm::TempMapping;
use crate::mm::{check_within_guest_mmap, virt_to_phys};
use crate::policy::register_policy_domain;
use crate::policy::userapp::{
    import_vmpl1_slot_vmsa_from_cpu, mark_app_fake_handoff_in_progress, register_user_app,
    try_kick_app, validate_launch_migration_version,
};
use crate::{kdebug, kerror, kinfo, kwarn, SELF_MAP};

verus! {

#[verifier::external_body]
fn read_guest_bytes(blob_gpa: PhysAddr, blob_len: usize) -> DekoGuestServResult<Vec<u8>> {
    if blob_len == 0 {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let aligned_gpa = blob_gpa.0 & !(PAGE_SIZE - 1);
    let page_offset = (blob_gpa.0 - aligned_gpa) as usize;
    let total_span = page_offset.checked_add(blob_len).ok_or(
        DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam),
    )?;
    let page_size = PAGE_SIZE as usize;
    let nr_pages = total_span.div_ceil(page_size);
    let last_page_gpa = aligned_gpa.checked_add(((nr_pages - 1) as u64) * PAGE_SIZE).ok_or(
        DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam),
    )?;

    if !check_within_guest_mmap(PhysAddr(aligned_gpa)) || !check_within_guest_mmap(
        PhysAddr(last_page_gpa),
    ) {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr));
    }
    let mapping = TempMapping::new(create_paddr_range(PhysAddr(aligned_gpa), nr_pages)).ok_or(
        DekoGuestServError::SoftError(DekoGuestServResultCode::Busy),
    )?;
    let src = unsafe {
        core::slice::from_raw_parts(
            (mapping.inner.start.0 as usize + page_offset) as *const u8,
            blob_len,
        )
    };
    let mut out = Vec::with_capacity_in(blob_len, DekoAllocatorApi {  });

    for byte in src {
        out.push(*byte);
    }

    Ok(out)
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
fn handle_deko_service_load_policy(params: &mut DekoGuestRequestParams) -> DekoGuestServResult<()> {
    let req_gpa = params.r9;
    let req_offset = req_gpa % PAGE_SIZE as u64;
    let req_body = req_gpa & !(PAGE_SIZE as u64 - 1);

    proof {
        let n = params.r9;

        assert(req_body % PAGE_SIZE == 0) by (bit_vector)
            requires
                req_body == (n & !((PAGE_SIZE as u64 - 1) as u64)),
                PAGE_SIZE == 0x1000,
        ;
    }

    if core::hint::unlikely(!check_within_guest_mmap(PhysAddr(req_body))) {
        kerror!("Load policy: request body NOT within guest mmap:", PhysAddr(req_body));
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if core::hint::unlikely(
        req_body >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE || core::mem::size_of::<
            DekoLoadPolicyReq,
        >() as u64 > PAGE_SIZE - req_offset,
    ) {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let req_mapping = TempMapping::new(create_paddr_range(PhysAddr(req_body), 1)).ok_or(
        DekoGuestServError::SoftError(DekoGuestServResultCode::Busy),
    )?;
    let req = *req_mapping.read_ref_at::<DekoLoadPolicyReq>(req_offset as usize);
    let blob_len = usize::try_from(req.blob_len).map_err(
        |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam),
    )?;
    kinfo!(
        "Load policy request: domain_id=",
        req.domain_id,
        " blob_gpa=",
        PhysAddr(req.blob_gpa),
        " blob_len=",
        blob_len,
    );
    let blob = read_guest_bytes(PhysAddr(req.blob_gpa), blob_len)?;
    kinfo!(
        "Load policy bytes copied: domain_id=",
        req.domain_id,
        " blob_len=",
        blob.len(),
    );
    register_policy_domain(req.domain_id, blob.as_slice())?;
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
        gpa.0 >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE || core::mem::size_of::<
            DekoMapIfcReq,
        >() as u64 > PAGE_SIZE as u64 - offset,
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

    let ext_vmpl1 = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).ext_vmpl1.as_ref().ok_or(
        DekoGuestServError::SoftError(DekoGuestServResultCode::Busy),
    )?;

    let ghcb_va = ext_vmpl1.ghcb.into_vaddr();
    let db_va =
        deko_rwlock_read_atomic_data!{
        ext_vmpl1.doorbell,
        doorbell,
        __,
        {
            doorbell.into_vaddr()
        }
    };

    req.ghcb_va = ghcb_va.0;
    req.db_va = db_va.0;
    temp_mapping.write_ref_at::<DekoMapIfcReq>(offset as _, &req);

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
fn handle_deko_service_launch_app(params: &mut DekoGuestRequestParams) -> DekoGuestServResult<u64> {
    let r9 = params.r9;
    let r9_offset = r9 % PAGE_SIZE as u64;
    let req_body = r9 & !0xfff;
    let expected_version = params.r8;
    let pid = (params.rdx & 0xffff_ffffu64) as u32;

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

    validate_launch_migration_version(pid, expected_version)?;

    try_kick_app(
        regs,
        PhysAddr(params.additional_data.unwrap().guest_cr3),
        pid,
        VirtAddr(params.rcx),
        params,
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

    if core::hint::unlikely(!check_within_guest_mmap(PhysAddr(req_body))) {
        kerror!("Report app: request body NOT within guest mmap:", PhysAddr(req_body));
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let offset = req_body % PAGE_SIZE as u64;
    let req_body = req_body & !0xfff;

    if core::hint::unlikely(
        req_body >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE || core::mem::size_of::<
            DekoNewAppReq,
        >() as u64 > PAGE_SIZE as u64 - offset,
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
    kinfo!(
        "report_app enter: pid=",
        req.tgid,
        " domain_id=",
        req.domain_id,
        " app_type=",
        req.app_type as u64,
        " is_creation=",
        is_creation,
        " guest_cr3=",
        PhysAddr(guest_cr3)
    );

    if let Err(err) = register_user_app(&mut req, PhysAddr(guest_cr3), is_creation) {
        kerror!(
            "report_app failed: pid=",
            req.tgid,
            " domain_id=",
            req.domain_id,
            " err=",
            err
        );
        return Err(err);
    }
    req_mapping.write_ref_at::<DekoNewAppReq>(offset as usize, &req);

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
fn handle_deko_service_task_migrate(params: &mut DekoGuestRequestParams) -> DekoGuestServResult<
    u64,
> {
    let req_gpa = params.r9;
    let req_offset = req_gpa % PAGE_SIZE as u64;
    let req_body = req_gpa & !0xfff;

    proof {
        let n = params.r9;

        assert(req_body % PAGE_SIZE == 0) by (bit_vector)
            requires
                req_body == (n & !((PAGE_SIZE as u64 - 1) as u64)),
                PAGE_SIZE == 0x1000,
        ;
    }

    if core::hint::unlikely(!check_within_guest_mmap(PhysAddr(req_body))) {
        kerror!("Task migrate: request body NOT within guest mmap:", PhysAddr(req_body));
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if core::hint::unlikely(
        req_body >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE || core::mem::size_of::<
            DekoTaskMigrateReq,
        >() as u64 > PAGE_SIZE - req_offset,
    ) {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let req_mapping = TempMapping::new(create_paddr_range(PhysAddr(req_body), 1)).ok_or(
        DekoGuestServError::SoftError(DekoGuestServResultCode::Busy),
    )?;
    let req = *req_mapping.read_ref_at::<DekoTaskMigrateReq>(req_offset as usize);
    let old_cpu = req.old_cpu;
    let new_cpu = req.new_cpu;
    let pid = req.pid;

    let (cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let this_cpu_id = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).cpu_id as u32;

    if core::hint::unlikely(this_cpu_id != new_cpu) {
        kwarn!(
            "Task migrate cpu mismatch: this_cpu=",
            this_cpu_id,
            " old_cpu=",
            old_cpu,
            " new_cpu=",
            new_cpu,
            " pid=",
            pid
        );
        return Ok(0);
    }
    if core::hint::unlikely(cpu.borrow(Tracked(&cpu_perm.ptr_perm)).ext_vmpl1.is_none()) {
        kwarn!(
            "Task migrate on cpu without VMPL1 context: cpu=",
            this_cpu_id,
            " pid=",
            pid
        );
        return Ok(0);
    }
    let _exported = import_vmpl1_slot_vmsa_from_cpu(pid, old_cpu)?;
    let version = mark_app_fake_handoff_in_progress(
        pid,
        old_cpu,
        req.user_gs_base,
        req.kernel_gs_base,
    )?;
    bind_current_cpu_vmpl1_slot(cpu, Tracked(&mut cpu_perm), pid);
    stage_fake_vmpl1_handoff_request(cpu, Tracked(&mut cpu_perm), pid, new_cpu, version);
    params.rdx = version;

    kdebug!(
        "Task migrate: staged fake handoff on cpu",
        this_cpu_id,
        " old_cpu=",
        old_cpu,
        " new_cpu=",
        new_cpu,
        " app_id=",
        pid,
        " version=",
        version
    );

    Ok(0)
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
) -> DekoGuestServResult<u64> {
    match req {
        DEKO_SERVICE_EXTEND_REPORT_APP => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_report_app(params)?;
            Ok(0)
        },
        DEKO_SERVICE_EXTEND_LAUNCH_APP => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_launch_app(params)
        },
        DEKO_SERVICE_EXTEND_LOAD_POLICY => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_load_policy(params)?;
            Ok(0)
        },
        DEKO_SERVICE_EXTEND_MAP_IFC => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_map_ifc(params)?;
            Ok(0)
        },
        DEKO_SERVICE_EXTEND_TASK_MIGRATE => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_task_migrate(params)
        },
        DEKO_SERVICE_EXTEND_INVOKE_UNTRUSTED_SYSCALL_HANDLER => Ok(0),
        DEKO_SERVICE_EXTEND_TIMER_EVENT => Ok(DEKO_SERVICE_TIMER),
        _ => {
            kerror!("Unsupported extend service request: ", req);
            Err(DekoGuestServError::SoftError(DekoGuestServResultCode::UnsupportedProtocol))
        },
    }
}

} // verus!
