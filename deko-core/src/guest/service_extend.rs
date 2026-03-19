use deko_std::address::{create_paddr_range, PhysAddr, VirtAddr};
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto, lemma_aligned_to_4k};
use deko_std::deko_rwlock_read_atomic_data;
use deko_std::mem::{PAGE_SIZE, PAGE_SIZE_2M, PERCPU_BASE};
use deko_std::prelude::{DekoAtomicData, VADDR_UPPER_MASK};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::cpu::regs::MSR_LSTAR;
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission, PERCPU_AREAS};
use crate::guest::service::TRAMPOLINE_PA;
use crate::guest::{
    bind_current_cpu_vmpl1_slot, guest_page_table, install_hook, stage_fake_vmpl1_handoff_request,
    DekoGuestLstarWriteReq, DekoGuestRequestParams, DekoGuestServError, DekoGuestServResult,
    DekoGuestServResultCode, DekoMapIfcReq, DekoMapIfcSingleReq, DekoNewAppReq, DekoTaskMigrateReq,
    PtRegs, DEKO_POLICY_ENGINE_BLOB, DEKO_SERVICE_EXTEND_INVOKE_UNTRUSTED_SYSCALL_HANDLER,
    DEKO_SERVICE_EXTEND_LAUNCH_APP, DEKO_SERVICE_EXTEND_MAP_IFC, DEKO_SERVICE_EXTEND_MSR_INTERCEPT,
    DEKO_SERVICE_EXTEND_REPORT_APP, DEKO_SERVICE_EXTEND_TASK_MIGRATE,
    DEKO_SERVICE_EXTEND_TIMER_EVENT, DEKO_SERVICE_TIMER,
};
use crate::mm::paging::strip_confidentiality_bits;
use crate::mm::vm::TempMapping;
use crate::mm::{check_within_guest_mmap, virt_to_phys};
use crate::policy::userapp::{
    import_vmpl1_slot_vmsa_from_cpu, mark_app_fake_handoff_in_progress, register_user_app,
    try_kick_app, validate_launch_migration_version,
};
use crate::{kdebug, kerror, kwarn, SELF_MAP};

verus! {

#[verus_spec(r =>

)]
fn handle_deko_service_lstar_intercept(
    params: &mut DekoGuestRequestParams,
    is_write: bool,
    guest_cr3: u64,
) -> DekoGuestServResult<()> {
    if is_write {
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
            core::mem::size_of::<DekoGuestLstarWriteReq>() as u64 > PAGE_SIZE as u64 - offset,
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
        kdebug!("Request:", req);

        let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
        let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
        let guest_cr3 = strip_confidentiality_bits(guest_cr3, cpu_borrow.private_bit);

        if !check_within_guest_mmap(PhysAddr(guest_cr3)) {
            kerror!("MSR intercept: guest CR3 NOT within guest mmap:", guest_cr3);
            kerror!("MSR intercept: cannot handle LSTAR MSR intercept without valid guest CR3");
            kerror!("MSR intercept: this is a serious security issue; aborting");

            return Err(DekoGuestServError::FatalError);
        }
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
        install_hook(
            guest_pgtable,
            syscall_enter_addr,
            cpu_borrow.private_bit,
            cpu_borrow.shared_bit,
            &req,
        )?;

        if let Some(_blob) = DEKO_POLICY_ENGINE_BLOB.get() {
            if req.trampoline_gva.0 % PAGE_SIZE as u64 != 0 {
                kerror!("MSR intercept: invalid trampoline gva for policy engine injection:", req.trampoline_gva => hex);
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
            }
            if req.trampoline_gva.0 <= VADDR_UPPER_MASK {
                kerror!("MSR intercept: trampoline gva for policy engine injection not in kernel space:", req.trampoline_gva => hex);
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
            }
        }
        lstar_req_mapping.write_ref_at::<DekoGuestLstarWriteReq>(offset as usize, &req);

        kdebug!("MSR intercept: LSTAR MSR intercept handled successfully");

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

    if params.rcx >= u32::MAX as u64 {
        kerror!("MSR intercept: invalid MSR index:", params.rcx);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    match params.rcx as u32 {
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
        DEKO_SERVICE_EXTEND_MSR_INTERCEPT => {
            kdebug!("MSR intercept:", params);

            proof_with!(Tracked(cpu_perm));
            handle_deko_service_msr_intercepts(params)?;
            Ok(0)
        },
        DEKO_SERVICE_EXTEND_REPORT_APP => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_report_app(params)?;
            Ok(0)
        },
        DEKO_SERVICE_EXTEND_LAUNCH_APP => {
            proof_with!(Tracked(cpu_perm));
            handle_deko_service_launch_app(params)
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
