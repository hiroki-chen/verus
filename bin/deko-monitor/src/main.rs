#![no_std]
#![no_main]
#![feature(proc_macro_hygiene)]

use deko_core::cpu::gdt::GLOBAL_GDT;
use deko_core::cpu::idt::{create_early_idt, init_early_idt, Idt};
use deko_core::cpu::regs::{cr0_init, cr4_init, load_cr3};
use deko_core::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use deko_core::elf::ElfFile;
use deko_core::mm::paging::{PageTable, PageTablePermission, PteFlags, GLOBAL};
use deko_core::mm::{virt_to_phys, DEKO_FRAME_ALLOCATOR};
use deko_core::{DekoKernelLaunchInfo, get_igvm_params, kinfo};
use deko_std::prelude::*;
use vstd::prelude::*;

core::arch::global_asm!(include_str!("../monitor.S"), options(att_syntax));

verus! {

#[inline]
#[verus_spec(r =>
    requires
        header.wf(),
)]
fn init_mem(header: &DekoKernelLaunchInfo) {
    let heap_start = header.heap_area_virt_start;
    let heap_size = header.heap_area_size;

    DEKO_FRAME_ALLOCATOR.0.init(heap_start, heap_size);
}

#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        header.wf(),
        elf.wf(),
)]
fn init_paging(
    header: &DekoKernelLaunchInfo,
    elf: &ElfFile,
    ms: &MappingSpace,
    private_bit: u64,
    shared_bit: u64,
) -> (DekoPPtr<PageTable>, PhysAddr, Tracked<PageTablePermission>) {
    let (new_page_table, paddr, Tracked(perm)) = PageTable::new(private_bit, shared_bit);

    // Now map the kernel ELF sections.
    let mut phys = header.kernel_region_phys_start;
    let seg_num = elf.load_segment_num(VirtAddr(header.kernel_region_virt_start));
    let mut i = 0;
    while i < seg_num
        invariant
            i <= seg_num,
            seg_num == elf.load_segments().len() as usize,
            elf.wf(),
            header.wf(),
            perm.wf(),
            phys % PAGE_SIZE == 0,
            phys <= 0x000f_ffff_ffff_f000,
            PAGE_SIZE == 0x1000,
        decreases seg_num - i,
    {
        let segment = elf.get_segment(i, VirtAddr(header.kernel_region_virt_start));
        let vaddr_start = segment.vaddr_range().start;
        let vaddr_end = segment.vaddr_range().end.page_align_up();
        let segment_len = vaddr_end.0 - vaddr_start.0;

        let flags = match (segment.exec(), segment.write()) {
            (true, false) => PteFlags::exec(),
            (false, true) => PteFlags::data(),
            _ => PteFlags::data_ro(),
        };

        proof {
            assume(perm.map_page_multiple_requires(
                new_page_table,
                vaddr_start..vaddr_end,
                PhysAddr(phys),
                ms,
                flags,
                private_bit,
                shared_bit,
            ));
        }

        PageTable::map_page_multiple(
            new_page_table,
            vaddr_start..vaddr_end,
            PhysAddr(phys),
            flags,
            ms,
            private_bit,
            shared_bit,
            Tracked(&mut perm),
        );

        i += 1;
        phys += segment_len;

        proof {
            assume(phys <= 0x000f_ffff_ffff_f000);
        }
    }

    // We then map the IGVM parameters.
    if header.igvm_params_virt_addr != 0 {
        proof {
            assume(
                VirtAddr(header.igvm_params_virt_addr).wf()
            );
            assume(ctx_perm.wf());
            assume(ctx_perm.pgtable_perm.mapped(VirtAddr(header.igvm_params_virt_addr)));

        }

        let igvms = #[verus_spec(with Tracked(ctx_perm))] deko_core::get_igvm_params(VirtAddr(header.igvm_params_virt_addr));
        let igvm_params_vaddr_start = VirtAddr(header.igvm_params_virt_addr);
        let igvm_size = igvms.size();
        proof {
            assume(header.igvm_params_virt_addr +igvm_size as u64 <= u64::MAX);
            assume(
                VirtAddr((header.igvm_params_virt_addr + igvm_size) as u64).page_align_up_requires()
            );
        }

        let igvm_params_vaddr_end =
            VirtAddr(header.igvm_params_virt_addr + igvms.size() as u64).page_align_up();
        let igvm_params_phys_start = PhysAddr(header.igvm_params_phys_addr);
        let flags = PteFlags::data();

        proof {
            assume(perm.map_page_multiple_requires(
                new_page_table,
                igvm_params_vaddr_start..igvm_params_vaddr_end,
                igvm_params_phys_start,
                ms,
                flags,
                private_bit,
                shared_bit,
            ));
        }

        PageTable::map_page_multiple(
            new_page_table,
            igvm_params_vaddr_start..igvm_params_vaddr_end,
            igvm_params_phys_start,
            flags,
            ms,
            private_bit,
            shared_bit,
            Tracked(&mut perm),
        );
    }

    (new_page_table, paddr, Tracked(perm))
}

/// The "true" entry point of the monitor.
///
/// This function does nothing but is just a small trampoline to call [`deko_setup`].
#[no_mangle]
#[verifier::exec_allows_no_decreases_clause]
#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<DekoCpuCtxPermission>,
    requires
        ctx_perm.wf_with(ctx),
        header.wf(),
)]
extern "C" fn deko_entry(ctx: DekoPPtr<DekoCpuCtx>, header: &DekoKernelLaunchInfo) -> ! {
    #[verus_spec(with Tracked(ctx_perm))]
    deko_setup(ctx, header);

    loop {
    }
}

/// Set up the environment for the DEKO itself. The reason why we
/// need this function is that the previous stage is just boostrapping
/// the CPU to a minimal environment and load kernel to the memory.
/// After that all the resources initialized are not available immediately
/// inside the kernel address spaces because the statics, page tables, etc.
/// reside in the lower half memory so we have to allocate/copy them to make
/// deko monitor work at this stage.
#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<DekoCpuCtxPermission>,
    requires
        ctx_perm.wf_with(ctx),
        header.wf(),
)]
fn deko_setup(ctx: DekoPPtr<DekoCpuCtx>, header: &DekoKernelLaunchInfo) {
    GLOBAL_GDT.load_selectors();

    let mut early_idt = Idt { entries: create_early_idt() };
    init_early_idt(&mut early_idt);

    let debug_serial_port = header.debug_serial_port;
    let secrets_page_virt = VirtAddr(header.secrets_page);

    // TODO: Copy the secrets page to the safe location.

    cr0_init();
    cr4_init();

    init_mem(header);

    let kernel_elf_len = header.kernel_elf_stage2_virt_end - header.kernel_elf_stage2_virt_start;
    let kernel_elf_bytes = deko_std::ptr::read_bytes(
        header.kernel_elf_stage2_virt_start,
        kernel_elf_len as usize,
    );
    let kernel_elf = match ElfFile::read(kernel_elf_bytes) {
        Some(elf) => elf,
        None => {
            kinfo!("Failed to read kernel ELF");
            early_die();
        },
    };

    // Since now we are inside the different address space we will need to
    // update the mapping space accordingly or physical addresses <-> virtual
    // addresses translation will panic.
    let kernel_mapping = FixedAddressMappingRange::new(
        VirtAddr(header.heap_area_virt_start),
        VirtAddr(header.heap_area_virt_start + header.heap_area_size),
        PhysAddr(header.heap_area_phys_start),
    );

    let ms = MappingSpace { kernel: kernel_mapping, physmap: Default::default() };

    let private_bit = ctx.borrow(Tracked(&ctx_perm.ptr_perm)).private_bit();
    let shared_bit = ctx.borrow(Tracked(&ctx_perm.ptr_perm)).shared_bit();

    let tracked mut ctx_perm = ctx_perm;
    let (new_page_table, paddr, Tracked(pgtable_perm)) = #[verus_spec(with Tracked(&mut ctx_perm))] init_paging(
        header,
        &kernel_elf,
        &ms,
        private_bit,
        shared_bit,
    );

    unsafe {
        // SAFETY: We have ensured that the new page table is valid because
        // init_paging() returns a valid page table and its permission.
        load_cr3(paddr);
    }

    // deko_core::hal::setup_env(ctx);
}

#[verifier::external]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    // Print detailed panic information using the logging system
    #[cfg(feature = "logging")]
    deko_core::logging::print_panic_info(info);

    unreachable!();
}

} // verus!
