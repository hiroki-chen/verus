#![no_std]
#![no_main]
#![feature(proc_macro_hygiene)]

use deko_core::cpu::gdt::GLOBAL_GDT;
use deko_core::cpu::idt::{create_early_idt, init_early_idt, Idt};
use deko_core::cpu::regs::{cr0_init, cr4_init, load_cr3};
use deko_core::cpu::{DekoCpuCtx, DekoCpuCtxPermission, PERCPU_AREAS};
use deko_core::elf::ElfFile;
use deko_core::mm::paging::{
    bit_not_in_addr_region, bit_not_overlapping, PageTable, PageTablePermission, PteFlags,
    Pte_ALL_BITS, GLOBAL,
};
use deko_core::mm::vm::{VirtualMemory, VirtualMemoryPermission, VirtualMemoryRegion, VMR_GRANULE};
use deko_core::mm::{virt_to_phys, DEKO_FRAME_ALLOCATOR};
use deko_core::{get_igvm_params, kinfo, DekoKernelLaunchInfo};
use deko_std::prelude::*;
use deko_std::snp::ghcb::GuestHostCommucationBlock;
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
        bit_not_in_addr_region(private_bit),
        bit_not_in_addr_region(shared_bit),
        bit_not_overlapping(private_bit),
        bit_not_overlapping(shared_bit),
        kernel_mapping == pgtable_perm.mapping_space,
)]
fn setup_bsp_cpu(
    init_pgtable: DekoPPtr<PageTable>,
    private_bit: u64,
    shared_bit: u64,
    kernel_mapping: MappingSpace,
) {
    broadcast use PteFlags::lemma_each_bit_is_valid;
    broadcast use PteFlags::lemma_from_bits_single;

    let shared_area_ptr = {
        let read_handle = PERCPU_AREAS.acquire_read();
        // The permission is discarded; you can only obtain this permission
        // if you own this.
        let (ptr, _) = read_handle.borrow().0.index_as_ptr(0);

        read_handle.release_read();

        ptr
    };

    // We first allocate a new CPU context for the BSP.
    let (bsp_ctx_ptr, Tracked(ctx_perm)) = {
        let (bsp_ctx_ptr, Tracked(ctx_perm)) = Box::<DekoCpuCtx>::new_zeroed(
            &DEKO_FRAME_ALLOCATOR.0,
        );
        bsp_ctx_ptr.into_ptr(Tracked(ctx_perm))
    };

    let (ghcb, Tracked(ghch_perm)) = {
        let (ghcb_ptr, Tracked(ghcb_perm)) = Box::<GuestHostCommucationBlock>::new_zeroed(
            &DEKO_FRAME_ALLOCATOR.0,
        );
        ghcb_ptr.into_ptr(Tracked(ghcb_perm))
    };

    // First step is to map itself.
    let vaddr = bsp_ctx_ptr.into_vaddr();
    let paddr = virt_to_phys(private_bit, shared_bit, vaddr, Tracked(&pgtable_perm));

    let cpu_start = PERCPU_BASE;
    // We resort to constants as somehow verus has issues dealing with large ranges.
    let cpu_end = PERCPU_END;
    let cpu_flags = PteFlags::kernel_code();  // P | G
    let cpu_self_flags = PteFlags::kernel_data();  // P | G | W

    proof {
        let cpu_start = cpu_start@;
        let cpu_end = cpu_end@;

        assert(0xFFFFFF8000000000 as u64 % VMR_GRANULE == 0 && 0xFFFFFF0000000000 as u64
            % VMR_GRANULE == 0) by (bit_vector);
        assert(cpu_flags.bits() & Pte_ALL_BITS == cpu_flags.bits() && cpu_self_flags.bits()
            & Pte_ALL_BITS == cpu_self_flags.bits()) by {
            bit_u64_and_auto();
        }
    }

    proof_with!(Tracked(pgtable_perm) => Tracked(vm_perm));
    let mut vm_region = VirtualMemoryRegion::new(
        cpu_start,
        cpu_end,
        cpu_flags,
        init_pgtable,
        kernel_mapping.clone(),
        private_bit,
        shared_bit,
    );

    // Create a mapping for the CPU area itself.
    let vm_block_for_self = VirtualMemory {
        range: cpu_start..cpu_end,
        paddr,
        flags: cpu_self_flags,
    };
    let tracked vm_block_perm = VirtualMemoryPermission {
        parent_id: vm_region.id@,
        range: cpu_start..cpu_end,
    };

    // TODO: There are some proofs. Insert into the region.
    // proof_with!(Tracked(&mut vm_perm), Tracked(vm_block_perm));
    // vm_region.insert(vm_block_for_self);

    let cpu_ctx = DekoCpuCtx::new(
        init_pgtable,
        shared_area_ptr,
        ghcb,
        0,
        shared_bit,
        private_bit,
        kernel_mapping,
        Some(vm_region),
    );

    // Finally we write the CPU context to the memory.
    bsp_ctx_ptr.write(Tracked(&mut ctx_perm), cpu_ctx);
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
#[allow(unreachable_code)]
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
