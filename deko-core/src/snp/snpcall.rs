use deko_std::prelude::*;
use deko_std::snp::ghcb::GuestHostCommucationBlock;
use vstd::cell::PCell;
use vstd::prelude::*;

use super::Snp;
use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::{
    DekoCpuCtx, DekoCpuCtxPermission, PerCpuAreas, PerCpuShared, CPUID_MAX_COUNT, CPU_AREA_MAGIC,
    PERCPU_AREAS,
};
use crate::mm::paging::PteFlags;
use crate::mm::{phys_to_virt, virt_to_phys, DEKO_FRAME_ALLOCATOR};
use crate::snp::ghcb::msr_register_ghcb_gpa;

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
    fn init_guest_host(
        &self,
        ctx: DekoPPtr<DekoCpuCtx>,
        Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
    )
        requires
            self.wf(),
            old(ctx_perm).wf_with(ctx),
        ensures
            ctx_perm.wf_with(ctx),
    {
        crate::snp::ghcb::validate_ghcb(ctx, Tracked(ctx_perm));
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

    pub fn init_each_cpu(
        &self,
        ctx: DekoPPtr<DekoCtx>,
        Tracked(ctx_perm): Tracked<DekoCtxPermission>,
    )
        requires
            self.wf(),
            ctx_perm.wf_with(ctx),
    {
        let shared_area_ptr = {
            let read_handle = PERCPU_AREAS.acquire_read();
            // The permission is discarded; you can only obtain this permission
            // if you own this.
            let (ptr, _) = read_handle.borrow().0.index_as_ptr(0);

            read_handle.release_read();

            ptr
        };

        // 1. First we set up the GHCB page for this CPU.
        // Get the page table from the context that was passed in
        let bsp_pgtable = ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).pgtable;
        let tracked bsp_pgtable_perm = &ctx_perm.pgtable_perm;
        let (ghcb, Tracked(ghcb_perm)) = Box::<GuestHostCommucationBlock>::new_zeroed(
            &DEKO_FRAME_ALLOCATOR.0,
        );
        let (ghcb, Tracked(ghcb_perm)) = ghcb.into_ptr(Tracked(ghcb_perm));

        // self.test_walk_ghcb();

        // 2. We now set up the percpu area for this CPU.
        // Note that we do not need to initialize the percpu area since it is
        // zeroed out by Box::new_zeroed.
        // We just need to set up the page table entry and the CpuData struct.
        let (bsp_percpu, Tracked(bsp_percpu_perm)) = Box::new_zeroed(&DEKO_FRAME_ALLOCATOR.0);
        let bsp_percpu_paddr = PhysAddr(bsp_percpu.addr() as u64);
        let (bsp_percpu_ptr, Tracked(mut bsp_percpu_perm)) = bsp_percpu.into_ptr(
            Tracked(bsp_percpu_perm),
        );

        // 3. Initialize the percpu area.
        // Get the platform-specific PTE mask values for this CPU
        let platform = Snp {  };
        let masks = platform.get_page_encryption_masks();

        // Use the existing context that was passed in from setup_env
        // This context already has the proper stage2_launch_info and other components
        let bsp_percpu = DekoCpuCtx::new(
            bsp_pgtable,
            shared_area_ptr,
            ghcb,
            0,  // cpu_id
            masks.shared_pte_mask,
            masks.private_pte_mask,
            ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).mapping_space,
        );
        bsp_percpu_ptr.write(Tracked(&mut bsp_percpu_perm), bsp_percpu);

        let tracked mut cpu_ctx_perm = DekoCpuCtxPermission {
            ptr_perm: bsp_percpu_perm,
            pgtable_perm: ctx_perm.pgtable_perm,
            ghcb_perm,
        };

        // TODO: CONSTRUCT THE PAIR.
        assume(cpu_ctx_perm.wf_with(bsp_percpu_ptr));

        // 4. This maps the PERCPU_BASE addr to the percpu area so `this_cpu` workds.
        DekoCpuCtx::map_page_4k(
            bsp_percpu_ptr,
            Tracked(&mut cpu_ctx_perm),
            PERCPU_BASE,
            bsp_percpu_paddr,
            PteFlags::data(),
        );

        self.init_guest_host(bsp_percpu_ptr, Tracked(&mut cpu_ctx_perm));
    }

    #[verifier::external_body]
    fn test_walk_ghcb(&self) {
        use crate::mm::paging::{index_at_level, Page, PteFlags};

        let page = unsafe { &*(core::ptr::addr_of!(crate::mm::paging::pgtable__) as *const Page) };

        let vaddr = VirtAddr(0x10000);

        let idx_lvl3 = index_at_level::<3>(vaddr);

        if page.0.0[idx_lvl3].0.0 & 0x8000000000027 != 0x8000000000027 {
            vstd::vpanic!("GHCB PTE level 3 mismatch");
        }
        let next_page_addr = ((page.0.0[idx_lvl3].0.0 & 0x000f_ffff_ffff_f000) & (!(1 << 51))) & !(1
            << 0);
        let next_page_addr2 = page.0.0[idx_lvl3].address(1 << 51, 1 << 0);

        if next_page_addr != next_page_addr2.0 {
            vstd::vpanic!("GHCB PTE level 3 address mismatch");
        }
    }

    // #[verifier::external_body]
    // pub fn heap_allocation_identity_check(addr: u64) {
    //     let vaddr = VirtAddr::new(addr);
    //     let paddr = virt_to_phys(vaddr);
    //     if paddr.0 != addr {
    //         vstd::vpanic!("Heap allocation is not identity mapped");
    //     }
    //     let pvaddr = phys_to_virt(paddr);
    //     if pvaddr.0 != addr {
    //         vstd::vpanic!("Heap allocation is not identity mapped");
    //     }
    // }
    // #[verifier::external_body]
    // pub fn ghcb_map_sanity_check(raw_addr: u64) {
    //     use crate::mm::paging::*;
    //     if raw_addr != 0x10000 {
    //         vstd::vpanic!("Invalid ghcb address");
    //     }
    //     let (ghcb, Tracked(ghcb_perm)) = crate::snp::ghcb::current_ghcb();
    //     if ghcb.addr() as u64 != raw_addr {
    //         vstd::vpanic!("GHCB mapping is incorrect");
    //     }
    //     let (pgtable, Tracked(pgtable_perm)) = DekoCpuCtx::get_current_pgtable();
    //     let mapping = PageTable::walk(
    //         pgtable,
    //         Tracked(&pgtable_perm),
    //         VirtAddr(ghcb.addr() as u64),
    //     );
    //     let Mapping::Level0(entry, Tracked(perm)) = mapping else {
    //         vstd::vpanic!("GHCB mapping is not a 4K page!");
    //     };
    //     if entry.borrow(Tracked(&perm)).0.0 & (1 << 51) != 0 {
    //         vstd::vpanic!("GHCB page is not shared!");
    //     }
    //     let address = entry.borrow(Tracked(&perm)).address().0;
    //     if address != (raw_addr & !(0xfff)) {  // address != raw_addr so we need to check .
    //         vstd::vpanic!("GHCB page address is incorrect!");
    //     }
    //     let flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&perm)).0.0);
    //     if !flags.contains(PRESENT) {
    //         vstd::vpanic!("GHCB page is not present!");
    //     }
    // }
    // /// Sanity check that the CPU page is mapped correctly.
    // #[verifier::external_body]
    // pub fn cpu_self_map_sanity_check(raw_addr: u64, ghcb_addr: u64) {
    //     use crate::mm::paging::*;
    //     if raw_addr < 0x10000 || raw_addr >= 0xa0000 {
    //         vstd::vpanic!("Invalid percpu address");
    //     }
    //     let (percpu, Tracked(percpu_perm)) = DekoCpuCtx::this_cpu();
    //     if percpu.addr() as u64 != PERCPU_BASE.0 {
    //         vstd::vpanic!("PERCPU_BASE mapping is incorrect");
    //     }
    //     let (pgtable, Tracked(pgtable_perm)) = DekoCpuCtx::get_current_pgtable();
    //     let mapping = PageTable::walk(
    //         pgtable,
    //         Tracked(&pgtable_perm),
    //         VirtAddr(percpu.addr() as u64),
    //     );
    //     let Mapping::Level0(entry, Tracked(perm)) = mapping else {
    //         vstd::vpanic!("Percpu mapping is not a 4K page!");
    //     };
    //     if entry.borrow(Tracked(&perm)).0.0 & (1 << 51) == 0 {
    //         vstd::vpanic!("Percpu page is shared!");
    //     }
    //     let address = entry.borrow(Tracked(&perm)).address().0;
    //     if address != raw_addr {
    //         vstd::vpanic!("Percpu page address is incorrect!");
    //     }
    //     let flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&perm)).0.0);
    //     if !flags.contains(PRESENT) {
    //         vstd::vpanic!("Percpu page is not present!");
    //     }
    //     let magic = percpu.borrow(Tracked(&percpu_perm.ptr_perm())).magic;
    //     if magic != CPU_AREA_MAGIC {
    //         vstd::vpanic!("Magic number mismatch: expected 0x114514, got
    //         {:#x}", magic);
    //     }
    //     let cpu_ctx = percpu.borrow(Tracked(&percpu_perm.ptr_perm()));
    //     let pgtable = cpu_ctx.pgtable(Tracked(&percpu_perm.ctx_perm()));
    //     if pgtable.addr() != pgtable.addr() {
    //         vstd::vpanic!("Percpu page table mismatch");
    //     }
    //     let ghcb = percpu.borrow(Tracked(&percpu_perm.ptr_perm())).ghcb();
    //     if ghcb.addr() as u64 != ghcb_addr {
    //         vstd::vpanic!("Percpu ghcb mismatch");
    //     }
    // }
    /// PVALIDATE takes a page size as an input parameter indicating that either a
    /// 4KB or 2MB page should be validated.
    ///
    /// If the guest attempts to validate a page that is not mapped to the specified size,
    /// e.g., a 4KB page is specified but the address is mapped to a 2MB page, a `VMEXIT`
    /// will occur to indicate an NPF. The reverse will generate a `FAIL_SIZE_MISMATCH`.
    ///
    /// Returns the return value and the changed bit of CF.
    #[verifier::external_body]
    pub fn pvalidate(
        vaddr: u64,
        psize: u64,
        validate: bool,
        Tracked(perm): Tracked<&mut DekoCtxPermission>,
    ) -> (r: (u64, bool))
        requires
            psize == 0x1000 || psize == 0x200000,  // Either 4K or 2M page.
            vaddr % 0x1000 == 0,
            old(perm).wf(),
        ensures
            perm.wf(),
            old(perm).deko_ctx_ptr_perm.pptr() === perm.deko_ctx_ptr_perm.pptr(),
            old(perm).private_bit() == perm.private_bit(),
            old(perm).shared_bit() == perm.shared_bit(),
    {
        let rax = vaddr;
        let ret: u64;
        let rcx = if psize == 0x1000 {
            RMP_4K
        } else {
            RMP_2M
        };
        let cf: u64;
        let rdx = if validate {
            1
        } else {
            0
        };

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

        (ret, cf == 0)
    }

    #[verifier::external_body]
    pub fn rmpadjust(
        vaddr: u64,
        psize: u64,
        Tracked(perm): Tracked<&mut DekoCtxPermission>,
    ) -> (ret: u64)
        requires
            old(perm).wf(),
        ensures
            perm.wf(),
            old(perm).deko_ctx_ptr_perm.pptr()
                === perm.deko_ctx_ptr_perm.pptr(),
    // todo: old(perm).rmpadjust_spec == perm.

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
