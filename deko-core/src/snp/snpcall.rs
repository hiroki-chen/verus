use deko_meta::IgvmParamBlock;
use deko_std::prelude::*;
use vstd::cell::PCell;
use vstd::prelude::*;

use super::Snp;
use crate::cpu::{
    CpuData, CpuDataPermission, PerCpuAreas, PerCpuShared, CPUID_MAX_COUNT, PERCPU_AREAS,
};
use crate::mm::paging::{box_into_ptr, get_initial_pgtable, DekoCpuPTOwner, PageTable, PteFlags, PERCPU_BASE};
use crate::mm::{phys_to_virt, virt_to_phys, DEKO_FRAME_ALLOCATOR};
use crate::snp::ghcb::{msr_register_ghcb_gpa, GuestHostCommucationBlock};

verus! {

pub const RMP_4K: u64 = 0;

pub const RMP_2M: u64 = 1;

pub const RMP_READ: u8 = 1;

pub const RMP_WRITE: u8 = 2;

pub const RMP_USER_EXE: u8 = 4;

pub const RMP_KERN_EXE: u8 = 8;

pub const RMP_NO_WRITE: u8 = RMP_READ | RMP_USER_EXE | RMP_KERN_EXE;

pub const RMP_RWX: u8 = RMP_NO_WRITE | RMP_WRITE;

impl Snp {
    /// Set up the GHCB pages and other necessary state for SNP operation.
    #[inline]
    fn init_guest_host(&self, cpu: DekoPPtr<CpuData>, Tracked(cpu_perm): Tracked<CpuDataPermission>)
        requires
            self.wf(),
            cpu_perm.wf_with(cpu),
    {
        let ghcb = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).ghcb();

        // The GHCB is allocated.
        GuestHostCommucationBlock::validate_ghcb(cpu, Tracked(cpu_perm));

        let ghcb_vaddr = VirtAddr::new(ghcb.addr() as u64);
        let ghcb_paddr = virt_to_phys(ghcb_vaddr);

        // Register the GHCB GPA with the hypervisor.
        msr_register_ghcb_gpa(ghcb_paddr);
    }

    pub fn init_platform_end(&self, igvm_params: &IgvmParamBlock)
        requires
            self.wf(),
            igvm_params.wf(),
    {
        let debug_console_port = igvm_params.debug_serial_port as u16;
        Self::init_ghcb_logging(debug_console_port);
        crate::logging::print_str("testtesttest");
    }

    pub fn init_each_cpu(&self)
        requires
            self.wf(),
    {
        let shared_area_ptr = {
            let read_handle = PERCPU_AREAS.acquire_read();
            // The permission is discarded; you can only obtain this permission
            // if you own this.
            let (ptr, _) = read_handle.borrow().0.index_as_ptr(0);

            read_handle.release_read();

            ptr
        };
        // Need inter-CPU communication block.
        // seems we should install the permission into the bsp cpu state.
        let (bsp_pgtable, Tracked(bsp_pgtable_perm)) = get_initial_pgtable();
        let pgowner = Ghost(DekoCpuPTOwner::new(0, bsp_pgtable@.addr() as u64));
        let (ghcb, Tracked(ghcb_perm)) = Box::<GuestHostCommucationBlock>::new_zeroed(
            &DEKO_FRAME_ALLOCATOR.0,
        );
        let (ghcb, Tracked(mut ghcb_perm)) = ghcb.into_ptr(Tracked(ghcb_perm));

        // FIXME: This creates a variable on the stack so this is problematic;
        let (bsp_percpu, Tracked(bsp_percpu_perm)) = Box::new_zeroed(&DEKO_FRAME_ALLOCATOR.0);
        let bsp_percpu_paddr = PhysAddr(bsp_percpu.addr() as u64); // note that this returns physical addr.
        let (bsp_percpu_ptr, Tracked(mut bsp_percpu_perm)) = box_into_ptr(bsp_percpu, Tracked(bsp_percpu_perm));

        // Initialize the percpu area.
        let bsp_percpu = CpuData::new(bsp_pgtable, shared_area_ptr, pgowner, 0, ghcb);
        bsp_percpu_ptr.write(Tracked(&mut bsp_percpu_perm), bsp_percpu);

        // This maps the PERCPU_BASE addr to the percpu area.
        PageTable::map_page(
            bsp_pgtable,
            Tracked(bsp_pgtable_perm),
            PERCPU_BASE,
            bsp_percpu_paddr,
            PteFlags::data(),
        );

        let Tracked(bsp_percpu_perm) = CpuDataPermission::upgrade(bsp_percpu_ptr, Tracked(bsp_percpu_perm));

        // The current allocation for bsp is problematic; let's just
        // avoid using this right now.
        self.init_guest_host(bsp_percpu_ptr, Tracked(bsp_percpu_perm));
    }

    #[verifier::external_body]
    fn test() {
    unsafe {

        use crate::mm::paging::*;

        let vaddr = PERCPU_BASE;

        // --- Level 3: PML4 Check (from physical address) ---
        let (pt, _) = get_initial_pgtable();
        let pml4_direct_ptr = pt.addr() as *const [u64; 512];
        
        let pml4_idx = (vaddr.0 >> 39) & 0x1ff; // Should be 510
        let pml4_entry = (*pml4_direct_ptr)[pml4_idx as usize];

        if pml4_entry & 1 == 0 {
            // If this fails, your mapping code didn't even create the top-level entry.
            vstd::vpanic!("DIRECT CHECK FAILED: PML4 Entry for PERCPU_BASE is not present. PML4[510] = {:x}", pml4_entry);
        }


        // --- Level 2: PDPT Check ---
        // Get the physical address of the PDPT from the PML4 entry

        // Convert it to a virtual address so we can read it
        // (This relies on the kernel's direct physical-to-virtual mapping)
        let pdpt_phys_addr = pml4_entry & 0x000f_ffff_ffff_f000;
        let pdpt_phys_addr = strip_confidentiality_bits(pdpt_phys_addr);
        let pdpt_phys_addr = strip_shared_address_bits(pdpt_phys_addr);

        // BUG: The pdpt_phys_addr does not reside within the mapped regions?
        let pdpt_virt_ptr = crate::mm::phys_to_virt(PhysAddr(pdpt_phys_addr)).0 as *const [u64; 512];

        let pdpt_idx = (vaddr.0 >> 30) & 0x1ff;
        let pdpt_entry = (*pdpt_virt_ptr)[pdpt_idx as usize];

        if pdpt_entry & (1 | (1 << 51) | (1 << 1) | (1 << 63)) == 0 {
            // If this fails, the PML4 entry was created, but the next level down was not.
            vstd::vpanic!("DIRECT CHECK FAILED: PDPT Entry for PERCPU_BASE is not present. Value = {:x}", pdpt_entry);
        }


        if pdpt_entry & (1 << 7) != 0 { /* Is it a 1G page? Not expected for this layout */ }


        // --- Level 1: Page Directory Check ---
        // Get the physical address of the Page Directory from the PDPT entry
        let pd_phys_addr = pdpt_entry & 0x000F_FFFF_FFFF_F000;
        let pd_phys_addr = strip_confidentiality_bits(pd_phys_addr);
        let pd_phys_addr = strip_shared_address_bits(pd_phys_addr);

        let pd_virt_ptr = crate::mm::phys_to_virt(PhysAddr(pd_phys_addr)).0 as *const [u64; 512];
        
        let pd_idx = (vaddr.0 >> 21) & 0x1ff;
        let pd_entry = (*pd_virt_ptr)[pd_idx as usize];

        if pd_entry & (1 | (1 << 51) | (1 << 1) | (1 << 63)) == 0 {
            vstd::vpanic!("DIRECT CHECK FAILED: Page Directory Entry for PERCPU_BASE is not present. Value = {:x}", pd_entry);
        }
        if pd_entry & (1 << 7) != 0 { /* Is it a 2M page? Possible. */ }


        // --- Level 0: Page Table Check ---
        // Get the physical address of the final Page Table from the PD entry
        let pt_phys_addr = pd_entry & 0x000F_FFFF_FFFF_F000;
        let pt_phys_addr = strip_confidentiality_bits(pt_phys_addr);
        let pt_phys_addr = strip_shared_address_bits(pt_phys_addr);
        let pt_virt_ptr = crate::mm::phys_to_virt(PhysAddr(pt_phys_addr)).0 as *const [u64; 512];

        let pt_idx = (vaddr.0 >> 12) & 0x1ff;
        let pt_entry = (*pt_virt_ptr)[pt_idx as usize];

        if pt_entry & (1 | (1 << 51) | (1 << 1) | (1 << 63)) == 0 {
            vstd::vpanic!("DIRECT CHECK FAILED: Final Page Table Entry for PERCPU_BASE is not present. Value = {:x}", pt_entry);
        }
        
        // correctly mapped now.
        // svsm's physical mapped addr : 0x8008000000014063
        let ptr = PERCPU_BASE.0 as *mut u32;
        core::ptr::write_volatile(ptr, 0xDEADBEEF);
        let val = core::ptr::read_volatile(ptr);
    }
    unsafe {

        }
    }

    /// PVALIDATE takes a page size as an input parameter indicating that either a
    /// 4KB or 2MB page should be validated.
    ///
    /// If the guest attempts to validate a page that is not mapped to the specified size,
    /// e.g., a 4KB page is specified but the address is mapped to a 2MB page, a `VMEXIT`
    /// will occur to indicate an NPF. The reverse will generate a `FAIL_SIZE_MISMATCH`.
    ///
    /// Returns the return value and the changed bit of CF.
    #[verifier::external_body]
    pub fn pvalidate(vaddr: u64, psize: u64, validate: bool, Tracked(perm): Tracked<()>) -> (r: (
        u64,
        bool,
    ))
        requires
            psize == 0x1000,
            vaddr % 0x1000
                == 0,
    // todo: add more requirements here since we can track permission of the memory.

    {
        let rax = vaddr;
        let ret: u64;
        let rcx = 0u64;  // as we do not support huge pages we just assume 0.
        let cf: u64;
        let rdx = validate as u64;

        unsafe {
            core::arch::asm!(
                "xorq %r8, %r8",
                "pvalidate",
                "adcq %r8, %r8",
                in("rax")  rax,
             in("rcx")  rcx,
             in("rdx")  rdx,
             lateout("rax") ret,
             lateout("r8") cf,
             options(att_syntax));
        }

        (ret, cf != 0)
    }

    #[verifier::external_body]
    pub fn rmpadjust(
        vaddr: u64,
        psize: u64,
        // attr: __RmpAttribute,
        Tracked(core): Tracked<CpuCore>,
        Tracked(core2): Tracked<CpuCore>,
        Tracked(perm): Tracked<()>,
    ) -> (ret: u64)
        requires
            true,
        ensures
            true,
    {
        let ret: u64;

        unsafe {
            core::arch::asm!(
                ".byte 0xf3,0x0f,0x01,0xf1",
                in("rax") vaddr, in("rcx") psize,
                lateout("rax") ret,
                options(nostack)
            );
        }

        ret
    }
}

} // verus!
