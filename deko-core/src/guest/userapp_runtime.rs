use deko_std::address::{create_paddr_range, PhysAddr, VirtAddr};
use deko_std::prelude::PAGE_SIZE;
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::cpu::regs::no_smap_zone;
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::guest::{
    DekoGuestRequestParams, DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode,
};
use crate::mm::paging::{bit_not_in_addr_region, strip_confidentiality_bits, PageTable};
use crate::mm::vm::TempMapping;
use crate::{kdebug, kinfo};

verus! {

#[verus_spec(r =>
    requires
        0 < from@,
        guest_cr3.wf(),
        guest_cr3@ % PAGE_SIZE == 0,
        guest_cr3@ + PAGE_SIZE < 0x000f_ffff_ffff_f000u64,
        from@ + len <= 0x8000_0000_0000,
)]
pub(crate) fn copy_from_user(
    guest_cr3: PhysAddr,
    from: VirtAddr,
    buf: *mut u8,
    len: usize,
) -> DekoGuestServResult<usize> {
    let offset_4k = from.0 & 0xfff;
    let offset_2m = from.0 & 0x1fffff;
    let from = VirtAddr(from.0 & (!0xfff));

    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let private_bit = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).private_bit;
    let shared_bit = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).shared_bit;
    let guest_cr3_p = strip_confidentiality_bits(guest_cr3.0, private_bit);

    proof {
        let cr3 = guest_cr3@;
        assert(guest_cr3_p <= cr3 && guest_cr3_p % PAGE_SIZE == 0) by (bit_vector)
            requires
                guest_cr3_p == cr3 & !(private_bit as u64),
                bit_not_in_addr_region(private_bit),
                cr3 % PAGE_SIZE == 0,
        ;
    }

    let guest_cr3 = TempMapping::new(create_paddr_range(PhysAddr(guest_cr3_p), 1)).ok_or(
        DekoGuestServError::SoftError(DekoGuestServResultCode::Busy),
    )?;

    let mapping = PageTable::walk_lvl3_guest(&guest_cr3, from, private_bit, shared_bit)?;
    if mapping.temp_mappings.len() <= 2 || mapping.temp_mappings.len() > 4 {
        kinfo!(
            "copy_from_user: unexpected number of temp mappings",
            mapping.temp_mappings.len()
        );
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let final_mapping = mapping.final_mapping().unwrap();
    let offset = if mapping.lvl == 0 {
        offset_4k
    } else {
        offset_2m
    };

    let addr = final_mapping.inner.start.0.wrapping_add(offset);
    let len = len.min(final_mapping.inner.end.0.wrapping_sub(addr) as usize);

    unsafe { copy_from_user_same_vmpl(final_mapping.inner.start.0.wrapping_add(offset), buf, len) }
}

#[verus_spec(r =>)]
#[inline(always)]
#[verifier::external_body]
unsafe fn copy_from_user_same_vmpl(addr: u64, buf: *mut u8, len: usize) -> DekoGuestServResult<
    usize,
> {
    kdebug!("copy_from_user_same_vmpl", addr =>hex, buf as u64 =>hex, len);

    no_smap_zone(
        ||
            {
                let src_ptr = addr as *const u8;
                let dst_ptr = buf;
                core::ptr::copy_nonoverlapping(src_ptr, dst_ptr, len);
            },
    );

    Ok(len)
}

pub(crate) fn bind_current_cpu_vmpl1_slot(
    cpu_ptr: DekoPPtr<DekoCpuCtx>,
    Tracked(cpu_perm0): Tracked<&mut DekoCpuCtxPermission>,
    pid: u32,
)
    requires
        old(cpu_perm0).wf_with(cpu_ptr),
        old(cpu_perm0).ptr_perm.value().ext_vmpl1 is Some,
    ensures
        cpu_perm0.wf_with(cpu_ptr),
        cpu_perm0.ptr_perm.value().ext_vmpl1 is Some,
{
    let cpu_id = cpu_ptr.borrow(Tracked(&cpu_perm0.ptr_perm)).cpu_id as u32;
    let mut cpu = cpu_ptr.take(Tracked(&mut cpu_perm0.ptr_perm));
    let mut ctx_vmpl1 = cpu.ext_vmpl1.take().unwrap();
    ctx_vmpl1.current_pid = Some(pid);
    ctx_vmpl1.slot_dirty = false;
    ctx_vmpl1.pending_export_pid = None;
    ctx_vmpl1.pending_export_target_cpu = None;
    ctx_vmpl1.pending_export_version = 0;
    cpu.ext_vmpl1 = Some(ctx_vmpl1);
    cpu_ptr.write(Tracked(&mut cpu_perm0.ptr_perm), cpu);

    kdebug!("Bound VMPL1 slot on cpu ", cpu_id, " to pid ", pid);
}

pub(crate) fn stage_fake_vmpl1_handoff_request(
    cpu_ptr: DekoPPtr<DekoCpuCtx>,
    Tracked(cpu_perm0): Tracked<&mut DekoCpuCtxPermission>,
    pid: u32,
    target_cpu: u32,
    version: u64,
)
    requires
        old(cpu_perm0).wf_with(cpu_ptr),
        old(cpu_perm0).ptr_perm.value().ext_vmpl1 is Some,
    ensures
        cpu_perm0.wf_with(cpu_ptr),
        cpu_perm0.ptr_perm.value().ext_vmpl1 is Some,
{
    let cpu_id = cpu_ptr.borrow(Tracked(&cpu_perm0.ptr_perm)).cpu_id as u32;
    let mut cpu = cpu_ptr.take(Tracked(&mut cpu_perm0.ptr_perm));
    let mut ctx_vmpl1 = cpu.ext_vmpl1.take().unwrap();
    ctx_vmpl1.current_pid = Some(pid);
    ctx_vmpl1.slot_dirty = false;
    ctx_vmpl1.pending_export_pid = Some(pid);
    ctx_vmpl1.pending_export_target_cpu = Some(target_cpu);
    ctx_vmpl1.pending_export_version = version;
    cpu.ext_vmpl1 = Some(ctx_vmpl1);
    cpu_ptr.write(Tracked(&mut cpu_perm0.ptr_perm), cpu);

    kdebug!(
        "Staged fake VMPL1 handoff request on cpu ",
        cpu_id,
        " pid=",
        pid,
        " target_cpu=",
        target_cpu,
        " version=",
        version
    );
}

} // verus!
