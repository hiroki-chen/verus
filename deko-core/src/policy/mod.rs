use deko_macros::DekoDebug;
use deko_std::address::{create_paddr_range, VirtAddr};
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto};
use deko_std::cpu::write_msr;
use deko_std::prelude::{
    func_ptr, DekoPointsTo, MappingSpace, PhysAddr, PAGE_SIZE, VADDR_UPPER_MASK,
};
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::cpu::DekoCpuCtx;
use crate::imp::{SnpStatusFlags, GUEST_MSR_INTERCEPT, MSR_SEV_STATUS};
use crate::mm::frame_allocator::DekoPageFrameBox;
use crate::mm::paging::{
    self, index_at_level, PageTable, PageTableEntry, PageTablePath, PageTablePermission,
    RECURSIVE_INDEX,
};
use crate::mm::vm::TempMapping;
use crate::mm::{virt_to_phys_checked, DEKO_FRAME_ALLOCATOR_FULL};
use crate::snp::vmsa::VMSA;
use crate::snp::SnpStatus;
use crate::{kerror, kinfo, kpanic_if};

pub(crate) mod msr;

core::arch::global_asm!(include_str!("trampoline.S"), options(att_syntax));

extern "C" {
    fn deko_trampoline_start();
    fn deko_trampoline_end();
    static mut deko_trampoline_data_entry: u64;
}

verus! {

func_ptr!(deko_trampoline_start);

func_ptr!(deko_trampoline_end);

#[inline(always)]
#[verifier::external_body]
pub fn update_syscall_entry(entry: u64) {
    unsafe {
        core::ptr::write_volatile(core::ptr::addr_of_mut!(deko_trampoline_data_entry), entry);
    }
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

/// The syscall hook function for guest running in the VM.
#[no_mangle]
pub fn syscall_hook() {
}

func_ptr!(syscall_hook);

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
        &[DekoMsrIntercept::InterceptMsrVec0(DekoMsrInterceptVec0::LstarWrite)],  // todo...
    // &[]
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
    with
        Tracked(g_pgtable_perm): Tracked<&PageTablePermission>,
    requires
        syscall_enter_addr.wf(),
        syscall_enter_addr@ >= VADDR_UPPER_MASK,
        g_pgtable_perm.wf(),
        g_pgtable_perm.pgtable_perm.pptr() == guest_pgtable@,
        private_bit == g_pgtable_perm.private_bit,
        shared_bit == g_pgtable_perm.shared_bit,
        ms == g_pgtable_perm.mapping_space,
        ms.wf(),
)]
pub fn install_hook(
    guest_pgtable: DekoPPtr<PageTable>,
    syscall_enter_addr: VirtAddr,
    private_bit: u64,
    shared_bit: u64,
    ms: MappingSpace,
) -> bool {
    broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;
    broadcast use PageTablePath::lemma_path_take_fact;
    broadcast use PageTablePath::lemma_drop_last;
    // Check if this is really mapped.

    if index_at_level::<3>(syscall_enter_addr) == RECURSIVE_INDEX as usize {
        // Any addresses starting with the recursive index are invalid
        // as they are either used for page table self-referencing or
        // not mapped at all.
        return false;
    }
    let g_syscall_entry = PageTable::walk(
        guest_pgtable,
        Tracked(g_pgtable_perm),
        syscall_enter_addr,
        &ms,
        private_bit,
        shared_bit,
    );

    // Not sure if Mapping::Level0 is valid but we just ignore it here.
    // If sometimes the guest really report Level0 then let's handle it later.
    match g_syscall_entry {
        paging::Mapping::Level1(ptr, idx) => {
            let ghost path: PageTablePath = PageTablePath::from_vaddr_at_level(
                syscall_enter_addr,
                2,
            ).normalize();
            proof {
                reveal_with_fuel(PageTablePath::remove_recursive_prefix, 10);
                assert(path.wf());
            }
            let tracked g_syscall_entry_perm = &g_pgtable_perm.storage.tracked_borrow(
                path,
            ).this_page_perm;
            let syscall_enter_paddr = ptr.borrow(Tracked(g_syscall_entry_perm)).0.index(
                idx,
            ).address(private_bit, shared_bit);

            // Here we request the guest to allocate a PML4 entry for us
            // to inject the trampoline code.
            //
            // Safety: We have already verified that the guest page table
            //         maps the syscall entry address.
            unsafe {
                patch_trampoline(syscall_enter_addr, syscall_enter_paddr);
            }

            true
        },
        _ => false,
    }
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
#[verus_spec(
    requires
        syscall_enter_addr.wf(),
        syscall_enter_addr@ >= VADDR_UPPER_MASK,
)]
unsafe fn patch_trampoline(syscall_enter_addr: VirtAddr, syscall_enter_paddr: PhysAddr) {
    const TSS_PAT: &'static [u8; 4] = &0x1111_1111u32.to_le_bytes();
    const STACK_PAT: &'static [u8; 4] = &0x2222_2222u32.to_le_bytes();

    kinfo!("Patching syscall trampoline at guest virtual address:", syscall_enter_addr);
    kinfo!("Corresponding physical address:", syscall_enter_paddr);

    // Create a temporary mapping for the Linux syscall code.
    let Some(temp_mapping) = TempMapping::new(create_paddr_range(syscall_enter_paddr, 1)) else {
        kerror!("Failed to create temporary mapping for syscall trampoline patching");
        return ;
    };

    let offset = syscall_enter_addr.0 & (PAGE_SIZE - 1);
    let code_size = PAGE_SIZE - offset;
    let trampoline_start = deko_trampoline_start as usize;
    let trampoline_end = deko_trampoline_end as usize;
    let trampoline_size = trampoline_end - trampoline_start;
    let source_code = core::slice::from_raw_parts(
        (temp_mapping.inner.start.0 as *const u8).add(offset as usize),
        code_size as usize,
    );
    kinfo!("Source:", source_code);

    kpanic_if!(
        !source_code.starts_with(&[0x0f, 0x01, 0xf8]),
        "Syscall trampoline code does not start with expected swapgs instruction",
    );

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
    }
    let mut tss_offset = None;
    let mut stack_offset = None;

    // Scan the source code to find the patterns.
    for i in 0..100 {
        if &source_code[i..i + 4] == &[0x65, 0x48, 0x89, 0x25] {
            let tss = u32::from_le_bytes(
                [source_code[i + 4], source_code[i + 5], source_code[i + 6], source_code[i + 7]],
            );
            kinfo!("Found TSS pattern at offset", i, "with value", tss => hex);
            tss_offset = Some(i + 4);
        } else if &source_code[i..i + 4] == &[0x65, 0x48, 0x8b, 0x25] {
            let stack = u32::from_le_bytes(
                [source_code[i + 4], source_code[i + 5], source_code[i + 6], source_code[i + 7]],
            );
            kinfo!("Found STACK pattern at offset", i, "with value", stack => hex);
            stack_offset = Some(i + 4);
        }
    }

    if tss_offset.is_none() || stack_offset.is_none() {
        kerror!("Failed to find pattern in the syscall source code");
        return ;
    }
    // Request one page for the trampoline buffer to store the
    // trampoline code and we will then make the change.
    //
    // Afterwards the buffer will be populated.

    let (trampoline_buf, _) = DekoPageFrameBox::<[u8; 0x1000]>::new_zeroed_in(
        &DEKO_FRAME_ALLOCATOR_FULL,
    );

    core::ptr::copy_nonoverlapping(
        trampoline_start as *const u8,
        trampoline_buf.addr() as *mut u8,
        trampoline_size,
    );

    deko_trampoline_data_entry = syscall_enter_addr.0 as u64;

    let code = core::slice::from_raw_parts_mut(
        trampoline_buf.addr() as *mut u8,
        trampoline_size as usize,
    );

    kinfo!("Original trampoline code:", code);

    // // Sliding window to find and patch the patterns.
    // for i in 0..(trampoline_size - 0x4) {
    //     if &code[i..i+4] == TSS_PAT {
    //         kinfo!("Patching TSS pattern at offset", i);
    //         code[i..i+4].copy_from_slice(&tss_offset.unwrap().to_le_bytes());

    //     } else if &code[i..i+4] == STACK_PAT {
    //         kinfo!("Patching STACK pattern at offset", i);

    //         code[i..i+4].copy_from_slice(&stack_offset.unwrap().to_le_bytes());
    //     }
    // }

    // kinfo!("Patched trampoline code:", code);

}

} // verus!
