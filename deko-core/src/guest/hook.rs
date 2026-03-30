use deko_std::address::{create_paddr_range, VirtAddr};
use deko_std::mem::PAGE_SIZE_2M;
use deko_std::prelude::{func_ptr, MappingSpace, PhysAddr, PAGE_SIZE, VADDR_UPPER_MASK};
use deko_std::sync::DekoAtomicData;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::cpu::DekoCpuCtx;
use crate::guest::{
    valid_kernel_vaddr, valid_trampoline_gpa, DekoGuestServError, DekoGuestServResult,
    DekoGuestServResultCode, DekoGuestTrampolineSetupReq,
};
use crate::mm::paging::{bit_not_in_addr_region, bit_not_overlapping, PageTable};
use crate::mm::vm::TempMapping;
use crate::policy::ifc::deko_ifc_entry_func_ptr;
use crate::policy::syscall::DEKO_VMPL1_SYSCALL_TRAMPOLINE;
use crate::snp::vmsa::VMSA;
use crate::{kerror, kinfo};

core::arch::global_asm!(
    concat!(include_str!("../asm/PER_CPU.offset"), "\n", include_str!("../asm/entry_SYSCALL_64.S")),
    options(att_syntax)
);

extern "C" {
    fn deko_trampoline_start();
    fn deko_sysret_window_start();
    fn deko_sysret_window_end();
    fn deko_trampoline_end();
    static mut deko_ifc_engine_entry: u64;
    static mut HV_SYSRET_WINDOW_START: u64;
    static mut HV_SYSRET_WINDOW_END: u64;
}

verus! {

pub const GUEST_TRAMPOLINE_PML4_HOLE: usize = 500;

pub const GUEST_TRAMPOLINE_MAGIC: &'static [u8; 15] = &[
    0x54u8,
    0x52,
    0x41,
    0x4d,
    0x50,
    0x4f,
    0x4c,
    0x49,
    0x4e,
    0x45,
    0x5f,
    0x49,
    0x4e,
    0x49,
    0x54,
];

func_ptr!(deko_trampoline_start);

func_ptr!(deko_trampoline_end);

#[inline(always)]
#[verifier::external_body]
#[doc(hidden)]
pub fn update_ifc_engine_entry(entry: u64) {
    unsafe {
        core::ptr::write_volatile(core::ptr::addr_of_mut!(deko_ifc_engine_entry), entry);
    }
}

#[verus_spec(
    requires
        syscall_enter_addr.wf(),
        syscall_enter_addr@ >= VADDR_UPPER_MASK,
        guest_pgtable.wf(),
        guest_pgtable.inner.end@ - guest_pgtable.inner.start@ == PAGE_SIZE,
        bit_not_overlapping(private_bit),
        bit_not_overlapping(shared_bit),
        bit_not_in_addr_region(private_bit),
        bit_not_in_addr_region(shared_bit),
)]
pub fn install_hook(
    guest_pgtable: TempMapping,
    syscall_enter_addr: VirtAddr,
    private_bit: u64,
    shared_bit: u64,
    req: &DekoGuestTrampolineSetupReq,
) -> DekoGuestServResult<()> {
    if !valid_kernel_vaddr(req.trampoline_gva) || !valid_trampoline_gpa(req.trampoline_gpa.0) {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let g_trampoline_mapping = PageTable::walk_lvl3_guest(
        &guest_pgtable,
        req.trampoline_gva,
        private_bit,
        shared_bit,
    )?;

    if g_trampoline_mapping.temp_mappings.len() <= 1 || g_trampoline_mapping.temp_mappings.len()
        > 4 {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let guest_trampoline_frame = g_trampoline_mapping.final_mapping().unwrap();
    move_to_guest(guest_trampoline_frame, syscall_enter_addr, req.trampoline_gva)?;

    g_trampoline_mapping.lock_translation_path()?;
    finish_install_hook(syscall_enter_addr);

    Ok(())
}

#[verus_spec()]
fn finish_install_hook(addr: VirtAddr) {
    let (this_cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();

    proof_with!(Tracked(&cpu_perm) => Tracked(mut vmsa_perm));
    let vmsa = VMSA::this_vmsa(this_cpu);

    proof_with!(Tracked(&mut vmsa_perm));
    VMSA::set_lstar(vmsa, addr.0)
}

#[verus_spec(r =>
    requires
        trampoline_gva.wf(),
        trampoline_gva@ % PAGE_SIZE == 0,
)]
pub(crate) fn inject_ifc_policy_engine(
    trampoline_gva: VirtAddr,
    blob_gpa: PhysAddr,
    payload: &[u8],
) -> DekoGuestServResult<()> {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let id = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).cpu_id;

    if id == 0 {
        let size_64m = 64 * 1024 * 1024;

        if core::hint::unlikely(
            size_64m < payload.len() || payload.len() == 0 || trampoline_gva.0 >= u64::MAX
                - size_64m as u64,
        ) {
            return Err(
                DekoGuestServError::fatal(
                    "inject_ifc_engine: invalid payload length or trampoline address",
                ),
            );
        }
        if core::hint::unlikely(blob_gpa.0 % PAGE_SIZE_2M != 0) {
            kerror!("IFC policy engine blob GPA is not page-aligned", blob_gpa => hex);
            return Err(
                DekoGuestServError::fatal("inject_ifc_engine: blob GPA is not page-aligned"),
            );
        }
        if core::hint::unlikely(blob_gpa.0 >= 0x0000_FFFF_FFFF_F000u64 - size_64m as u64) {
            kerror!("IFC policy engine blob GPA exceeds canonical address space", blob_gpa => hex);
            return Err(
                DekoGuestServError::fatal(
                    "inject_ifc_engine: blob GPA exceeds canonical address space",
                ),
            );
        }
        let ifc_start_va = VirtAddr(trampoline_gva.0 + PAGE_SIZE_2M);
        let len = payload.len() as u64 / PAGE_SIZE + 1;
        kinfo!(
            "Injecting IFC policy engine of size",
            payload.len(),
            "bytes into guest at",
            ifc_start_va,
            "with blob GPA",
            blob_gpa,
        );

        let Some(temp_mapping) = TempMapping::new(create_paddr_range(blob_gpa, len as usize)) else {
            kerror!("Failed to create temporary mapping for IFC policy engine blob");
            return Err(
                DekoGuestServError::fatal("inject_ifc_engine: failed to create temporary mapping"),
            );
        };

        temp_mapping.copy_bytes_from(payload);
    }
    Ok(())
}

#[verifier::spinoff_prover]
#[verus_spec(r =>
    requires
        guest_trampoline_frame.wf(),
        syscall_enter_addr.wf(),
        syscall_enter_addr@ >= VADDR_UPPER_MASK,
        trampoline_gva.wf(),
        trampoline_gva@ >= VADDR_UPPER_MASK,
        guest_trampoline_frame.inner.end@ - guest_trampoline_frame.inner.start@ >= PAGE_SIZE,
)]
fn move_to_guest(
    guest_trampoline_frame: &TempMapping,
    syscall_enter_addr: VirtAddr,
    trampoline_gva: VirtAddr,
) -> DekoGuestServResult<()> {
    assume(core::mem::size_of::<[u8; 15]>() == 15);

    let magic = guest_trampoline_frame.read_ref::<[u8; 15]>();
    if !<[u8; 15] as PartialEq>::eq(magic, GUEST_TRAMPOLINE_MAGIC) {
        kerror!("Trampoline code magic does not match expected value", magic, GUEST_TRAMPOLINE_MAGIC);

        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    unsafe { patch_trampoline(syscall_enter_addr, trampoline_gva, guest_trampoline_frame) }
}

#[verifier::external_body]
#[verus_spec(r =>
    requires
        syscall_enter_addr.wf(),
        syscall_enter_addr@ >= VADDR_UPPER_MASK,
        g_trampoline.wf(),
        trampoline_gva.wf(),
        trampoline_gva@ >= VADDR_UPPER_MASK,
)]
unsafe fn patch_trampoline(
    syscall_enter_addr: VirtAddr,
    trampoline_gva: VirtAddr,
    g_trampoline: &TempMapping,
) -> DekoGuestServResult<()> {
    let trampoline_start = deko_trampoline_start as *const () as usize;
    let trampoline_end = deko_trampoline_end as *const () as usize;
    let trampoline_size = trampoline_end - trampoline_start;
    if trampoline_size > PAGE_SIZE as usize {
        kerror!(
            "Trampoline size",
            trampoline_size,
            "exceeds page size",
            PAGE_SIZE,
        );

        return Err(
            DekoGuestServError::fatal("patch_trampoline: trampoline size exceeds page size"),
        );
    }
    update_ifc_engine_entry(deko_ifc_entry_func_ptr() as u64);

    let sysret_window_start_off = (deko_sysret_window_start as *const () as usize).wrapping_sub(
        trampoline_start,
    );
    let sysret_window_end_off = (deko_sysret_window_end as *const () as usize).wrapping_sub(
        trampoline_start,
    );

    unsafe {
        HV_SYSRET_WINDOW_START = trampoline_gva.0.wrapping_add(sysret_window_start_off as u64);
        HV_SYSRET_WINDOW_END = trampoline_gva.0.wrapping_add(sysret_window_end_off as u64);
    }

    core::ptr::copy_nonoverlapping(
        trampoline_start as *const u8,
        g_trampoline.inner.start.0 as *mut u8,
        trampoline_size,
    );

    DEKO_VMPL1_SYSCALL_TRAMPOLINE.init(DekoAtomicData::new(trampoline_gva));
    kinfo!(
        "Installed syscall trampoline:",
        "syscall_enter=",
        syscall_enter_addr,
        " trampoline_gva=",
        trampoline_gva,
        " size=",
        trampoline_size,
    );

    Ok(())
}

} // verus!
