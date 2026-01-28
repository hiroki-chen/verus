use deko_macros::DekoDebug;
use deko_std::address::{create_paddr_range, VirtAddr};
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto};
use deko_std::cpu::write_msr;
use deko_std::mem::PAGE_SIZE_2M;
use deko_std::prelude::{
    func_ptr, DekoPointsTo, MappingSpace, PhysAddr, PAGE_SIZE, VADDR_UPPER_MASK,
};
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use deko_std::with_permission;
use vstd::prelude::*;

use crate::cpu::DekoCpuCtx;
use crate::guest::service::DekoGuestLstarWriteReq;
use crate::guest::{DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode};
use crate::imp::{RmpFlags, SnpStatusFlags, GUEST_MSR_INTERCEPT, MSR_SEV_STATUS};
use crate::mm::frame_allocator::DekoPageFrameBox;
use crate::mm::paging::{
    self, bit_not_in_addr_region, bit_not_overlapping, index_at_level, index_at_level_spec,
    PageTable, PageTableEntry, PageTablePath, PageTablePermission, PteFlags, RECURSIVE_INDEX,
};
use crate::mm::vm::TempMapping;
use crate::mm::{virt_to_phys, virt_to_phys_checked, DEKO_FRAME_ALLOCATOR_FULL};
use crate::snp::vmsa::VMSA;
use crate::snp::SnpStatus;
use crate::{kerror, kinfo, kpanic_if};

pub(crate) mod guest_paging;
pub(crate) mod labels;
pub(crate) mod msr;
pub(crate) mod syscall;
pub(crate) mod userapp;

core::arch::global_asm!(include_str!("trampoline.S"), options(att_syntax));

extern "C" {
    fn deko_trampoline_start();
    fn deko_trampoline_end();
    static mut deko_trampoline_data_entry: u64;
}

verus! {

/// The policy engine is responsible for enforcing security policies.
#[derive(DekoDebug)]
pub struct DekoPolicyEngine {}

/// A policy domain represents a security boundary within which certain
/// policies are enforced.
///
/// You can think of a policy domain as a sandboxed environment where
/// specific security rules and restrictions apply to the code and data
/// operating within that domain.
#[derive(DekoDebug)]
pub struct DekoPolicyDomain {}

with_permission!(
    DekoPolicyDomain,
);

#[repr(C, align(8))]
#[derive(DekoDebug, Clone, Copy)]
pub struct DekoSyscallBody {
    #[deko(hex)]
    pub rax: u64,  // Syscall number
    #[deko(hex)]
    pub rdi: u64,  // Arg 1
    #[deko(hex)]
    pub rsi: u64,  // Arg 2
    #[deko(hex)]
    pub rdx: u64,  // Arg 3
    #[deko(hex)]
    pub r10: u64,  // Arg 4
    #[deko(hex)]
    pub r8: u64,  // Arg 5
    #[deko(hex)]
    pub r9: u64,  // Arg 6
    #[deko(hex)]
    pub rcx: u64,  // Return Address
    #[deko(hex)]
    pub r11: u64,  // RFLAG
    // The current cr3.
    #[deko(hex)]
    pub cr3: u64,
}

impl WellFormed for DekoSyscallBody {
    open spec fn wf(&self) -> bool {
        true
    }
}

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
pub fn update_syscall_entry(entry: u64) {
    unsafe {
        core::ptr::write_volatile(core::ptr::addr_of_mut!(deko_trampoline_data_entry), entry);
    }
}

/// See AMD's manual. Table B-1. VMCB Layout
///
/// The intercept field in the VMSA area is the same as in the VMCB.
/// We also define this an enum to align with other intercept enums.
#[repr(u32)]
#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub enum DekoInterceptVec0 {
    Cr3Read = 1 << 3,
    Cr3Write = 1 << (3 + 16),
}

/// See AMD's manual. Table B-3. INTERCEPT_VEC2 Layout
///
/// This is for intercepting the excepton vectors.
#[repr(u32)]
#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub enum DekoInterceptVec2 {
    PageFault = 1 << 14,
}

/// See AMD's manual. Table B-5. INTERCEPT_MSR_VEC0 Layout
#[repr(u32)]
#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub enum DekoMsrInterceptVec0 {
    StarRead = 8,
    StarWrite = 9,
    LstarRead = 10,
    LstarWrite = 11,
    CstarRead = 12,
    CstarWrite = 13,
}

#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub enum DekoMsrIntercept {
    /// Intercept for MSR vector 0.
    InterceptMsrVec0(DekoMsrInterceptVec0),
}

#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub enum DekoIntercept {
    /// Intercept for intercept vector 0.
    InterceptVec0(DekoInterceptVec0),
    /// Intercept for intercept vector 2.
    InterceptVec2(DekoInterceptVec2),
}

#[verus_verify]
impl VMSA {
    /// Enable MSR intercept for the given MSR `which`.
    ///
    /// Call this function only after the vmsa page has been properly allocated
    /// and mapped on the current CPU.
    #[verifier::external_body]
    #[verus_spec(
        with
            Tracked(vmsa_perm): Tracked<&mut DekoPointsTo<Self>>,
        requires
            old(vmsa_perm).is_init(),
            old(vmsa_perm).wf(),
            old(vmsa_perm).pptr() == ptr@,
        ensures
            vmsa_perm.is_init(),
            vmsa_perm.wf(),
            vmsa_perm.pptr() == ptr@,
    )]
    pub fn enable_msr_intercept(ptr: DekoPPtr<Self>, intercepts: &[DekoMsrIntercept]) {
        if !check_and_enable_msr_intercept_support() {
            kerror!("SEV-SNP Guest MSR Intercept not supported on this platform");

            return ;
        }
        unsafe {
            let vmsa = ptr.addr() as *mut VMSA;

            let vmpl_ptr = core::ptr::addr_of_mut!((*vmsa).vmpl);
            let current_vmpl = core::ptr::read_unaligned(vmpl_ptr);
            if current_vmpl != 2 {
                // VMPL 0 cannot set MSR intercepts.
                kinfo!("VMPL 0 cannot set MSR intercepts in VMSA");
                return ;
            }
            let vec_ptrs = core::ptr::addr_of_mut!((*vmsa).intercept_msr_vecs);

            for i in 0..intercepts.len() {
                let which = intercepts[i];

                match which {
                    DekoMsrIntercept::InterceptMsrVec0(vec0) => {
                        let bit = vec0 as u64;
                        let vec0_ptr = (vec_ptrs as *mut u64).add(0);
                        let mut current_val = core::ptr::read_unaligned(vec0_ptr);
                        current_val |= 1 << bit;
                        core::ptr::write_unaligned(vec0_ptr, current_val);
                    },
                }
            }
        }
    }
}

/// Note that the bit `GuestinterceptCtl` may only be used if
/// "Allowed SEV Features" is enabled and the `Allowed SEV Features Mask`
/// permits the use of this feature.
#[inline]
pub fn check_and_enable_msr_intercept_support() -> bool {
    broadcast use SnpStatusFlags::lemma_each_bit_is_valid;

    proof {
        bit_u32_and_auto();
        bit_u64_and_auto();
    }

    let sev_features = SnpStatusFlags::get_status();
    sev_features.contains(GUEST_MSR_INTERCEPT)
}

/// Enable the syscall hook for guest running in the VM.
///
/// This is done by enabling the appropriate bit mask in the VMSA's intercept_msr_vec.
#[verus_spec()]
pub fn enable_syscall_hook() {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    proof_with!(Tracked(&cpu_perm) => Tracked(mut vmsa_perm));
    let vmsa = VMSA::this_vmsa(cpu);

    // Now enable the syscall hook by setting the appropriate bit in the intercept_msr_vec.
    proof_with!(Tracked(&mut vmsa_perm));
    VMSA::enable_msr_intercept(
        vmsa,
        &[DekoMsrIntercept::InterceptMsrVec0(DekoMsrInterceptVec0::LstarWrite)],
    );
}

/// Installs the syscall hook and locks down the guest entry page.
///
/// **Note**: The caller must provide the valid guest page table mapping for the syscall entry.
///
/// This operation enforces RMP permission restrictions (typically RX) on the syscall entry
/// page to prevent the guest from remapping or overwriting the hook. After successfully
/// installing the hook, it updates `VMSA.intercept_msr_vecs[0]` to disable the now-redundant
/// `WRMSR` interception.
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
    req: &DekoGuestLstarWriteReq,
) -> DekoGuestServResult<()> {
    if req.trampoline_gva.0 < VADDR_UPPER_MASK || req.trampoline_gpa.0 % PAGE_SIZE != 0
        || req.trampoline_gpa.0 >= 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE_2M {
        // Guest trampoline virtual address must be in the higher half
        // of the address space.
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let g_trampoline_mapping = PageTable::walk_lvl3_guest(
        &guest_pgtable,
        req.trampoline_gva,
        private_bit,
        shared_bit,
    )?;

    if g_trampoline_mapping.temp_mappings.len() <= 1 || g_trampoline_mapping.temp_mappings.len()
        > 3 {
        // We need at least two levels of page table mappings.
        // LEVEL1 => HUGE and LEVEL0 => NORMAL
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let guest_trampoline_frame = g_trampoline_mapping.final_mapping().unwrap();
    move_to_guest(guest_trampoline_frame, syscall_enter_addr)?;
    finish_install_hook(req.trampoline_gva);

    // And then we lock down the guest syscall entry page
    g_trampoline_mapping.lock_translation_path()
}

#[verus_spec()]
fn finish_install_hook(addr: VirtAddr) {
    let (this_cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();

    proof_with!(Tracked(&cpu_perm) => Tracked(mut vmsa_perm));
    let vmsa = VMSA::this_vmsa(this_cpu);

    // Now we write the LSTAR MSR to point to our trampoline code.
    proof_with!(Tracked(&mut vmsa_perm));
    VMSA::set_lstar(vmsa, addr.0)
}

/// Injects the payload of the IFC policy engine into the guest memory.
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
    let size_64m = 64 * 1024 * 1024;

    if core::hint::unlikely(
        size_64m < payload.len() || payload.len() == 0 || trampoline_gva.0 >= u64::MAX
            - size_64m as u64,
    ) {
        return Err(DekoGuestServError::FatalError);
    }
    if core::hint::unlikely(blob_gpa.0 % PAGE_SIZE_2M != 0) {
        kerror!("IFC policy engine blob GPA is not page-aligned", blob_gpa => hex);
        return Err(DekoGuestServError::FatalError);
    }
    if core::hint::unlikely(blob_gpa.0 >= 0x0000_FFFF_FFFF_F000u64 - size_64m as u64) {
        kerror!("IFC policy engine blob GPA exceeds canonical address space", blob_gpa => hex);
        return Err(DekoGuestServError::FatalError);
    }
    // Now we need to copy all the bytes to that area.

    let ifc_start_va = VirtAddr(trampoline_gva.0 + PAGE_SIZE_2M);
    let len = payload.len() as u64 / PAGE_SIZE + 1;
    kinfo!(
        "Injecting IFC policy engine of size",
        payload.len(),
        "bytes into guest at",
        ifc_start_va => hex);

    let Some(temp_mapping) = TempMapping::new(create_paddr_range(blob_gpa, len as usize)) else {
        kerror!("Failed to create temporary mapping for IFC policy engine blob");
        return Err(DekoGuestServError::FatalError);
    };

    temp_mapping.copy_bytes_from(payload);

    Ok(())
}

/// Move the trampoline code into the guest prepared page.
///
/// The `guest_trampoline_frame` is the temporary mapping of the guest page
/// where we will copy the trampoline code to.`
#[verifier::spinoff_prover]
#[verus_spec(r =>
    requires
        guest_trampoline_frame.wf(),
        syscall_enter_addr.wf(),
        syscall_enter_addr@ >= VADDR_UPPER_MASK,
        guest_trampoline_frame.inner.end@ - guest_trampoline_frame.inner.start@ == PAGE_SIZE,
)]
fn move_to_guest(
    guest_trampoline_frame: &TempMapping,
    syscall_enter_addr: VirtAddr,
) -> DekoGuestServResult<()> {
    // This is awkward
    assume(core::mem::size_of::<[u8; 15]>() == 15);

    // Now we check the content the trampoline code.
    let magic = guest_trampoline_frame.read_ref::<[u8; 15]>();
    if !<[u8; 15] as PartialEq>::eq(magic, GUEST_TRAMPOLINE_MAGIC) {
        kerror!("Trampoline code magic does not match expected value", magic, GUEST_TRAMPOLINE_MAGIC);

        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    // Here we request the guest to allocate a PML4 entry for us
    // to inject the trampoline code.
    //
    // Safety: We have already verified that the guest page table
    //         maps the syscall entry address.

    unsafe { patch_trampoline(syscall_enter_addr, guest_trampoline_frame) }
}

/// Patch the incomplete trampoline code with the real entry point
/// and other runtime-only data.
///
/// # Safety
///
/// The caller must ensure that the `syscall_enter_addr` is properly
/// mapped in the guest page table and that the `syscall_enter_paddr`
/// is the correct physical address corresponding to `syscall_enter_addr`.
///
/// ↑ can be added into the spec.
#[verifier::external_body]
#[verus_spec(r =>
    requires
        syscall_enter_addr.wf(),
        syscall_enter_addr@ >= VADDR_UPPER_MASK,
        g_trampoline.wf(),
)]
unsafe fn patch_trampoline(
    syscall_enter_addr: VirtAddr,
    g_trampoline: &TempMapping,
) -> DekoGuestServResult<()> {
    let trampoline_start = deko_trampoline_start as usize;
    let trampoline_end = deko_trampoline_end as usize;
    let trampoline_size = trampoline_end - trampoline_start;
    if trampoline_size > PAGE_SIZE as usize {
        // Trampoline code should fit within a single page for
        // best performance and simplicity.
        //
        // This is not a fatal error though.
        kerror!(
            "Trampoline size",
            trampoline_size,
            "exceeds page size",
            PAGE_SIZE,
        );

        return Err(DekoGuestServError::FatalError);
    }
    update_syscall_entry(syscall_enter_addr.0 as u64);

    core::ptr::copy_nonoverlapping(
        trampoline_start as *const u8,
        g_trampoline.inner.start.0 as *mut u8,
        trampoline_size,
    );

    Ok(())
}

} // verus!
