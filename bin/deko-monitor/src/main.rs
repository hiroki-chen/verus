#![no_std]
#![no_main]
#![feature(proc_macro_hygiene)]

use deko_core::cpu::gdt::GLOBAL_GDT;
use deko_core::cpu::idt::{create_early_idt, init_early_idt, Idt};
use deko_core::cpu::regs::{cr0_init, cr4_init, load_cr3};
use deko_core::cpu::{DekoCpuCtx, DekoCpuCtxPermission, PERCPU_AREAS};
use deko_core::elf::ElfFile;
use deko_core::mm::paging::{PageTable, PageTablePermission, PteFlags, GLOBAL};
use deko_core::mm::{virt_to_phys, DEKO_FRAME_ALLOCATOR};
use deko_core::{get_igvm_params, kinfo, DekoKernelLaunchInfo};
use deko_std::prelude::*;
use vstd::prelude::*;

core::arch::global_asm!(include_str!("../monitor.S"), options(att_syntax));

verus! {

#[verus_spec(r =>
    with
        Tracked(pgtable_perm): Tracked<PageTablePermission>,
    requires
        pgtable_perm.private_bit == private_bit,
        pgtable_perm.shared_bit == shared_bit,
        pgtable_perm.mapping_space == kernel_mapping,
        kernel_mapping.wf(),
        pgtable_perm.wf(),
        pgtable_perm.pgtable_perm.pptr() == init_pgtable@,
)]
fn setup_bsp_cpu(
    init_pgtable: DekoPPtr<PageTable>,
    private_bit: u64,
    shared_bit: u64,
    kernel_mapping: MappingSpace,
) {
    // We first allocate a new CPU context for the BSP.
    let (bsp_ctx_ptr, Tracked(ctx_perm)) = {
        let (bsp_ctx_ptr, Tracked(ctx_perm)) = Box::<DekoCpuCtx>::new_zeroed(
            &DEKO_FRAME_ALLOCATOR.0,
        );
        bsp_ctx_ptr.into_ptr(Tracked(ctx_perm))
    };

    // First step is to map itself.
    let vaddr = bsp_ctx_ptr.into_vaddr();
    let paddr = virt_to_phys(private_bit, shared_bit, vaddr, Tracked(&pgtable_perm));

    // let deko_cpu_ctx = DekoCpuCtx::new(pgtable, shared_area, ghcb, cpu_id, shared_bit, private_bit, kernel_mapping);
}

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
///
/// At early stage the panic information will not be properly printed so
/// a Qemu crash is expected if anything goes wrong here before the full
/// logging system (if enabled) is set up.
#[verifier::exec_allows_no_decreases_clause]
#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<DekoCpuCtxPermission>,
    requires
        ctx_perm.wf_with(ctx),
        header.wf(),
)]
fn deko_setup(ctx: DekoPPtr<DekoCpuCtx>, header: &DekoKernelLaunchInfo) -> ! {
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

    let ms = MappingSpace { kernel: kernel_mapping, physmap: FixedAddressMappingRange::dummy() };

    let private_bit = ctx.borrow(Tracked(&ctx_perm.ptr_perm)).private_bit();
    let shared_bit = ctx.borrow(Tracked(&ctx_perm.ptr_perm)).shared_bit();

    let tracked mut ctx_perm = ctx_perm;

    let (new_page_table, paddr, Tracked(pgtable_perm)) = #[verus_spec(with Tracked(&mut ctx_perm))]
    deko_core::mm::paging::init_monitor_paging(header, &kernel_elf, &ms, private_bit, shared_bit);

    unsafe {
        // SAFETY: We have ensured that the new page table is valid because
        // init_paging() returns a valid page table and its permission.
        load_cr3(paddr);
    }

    // Prepare the BSP CPU context.
    #[verus_spec(with Tracked(pgtable_perm))]
    setup_bsp_cpu(new_page_table, private_bit, shared_bit, ms);

    loop {
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
