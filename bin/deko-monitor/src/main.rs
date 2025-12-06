#![no_std]
#![no_main]
#![feature(proc_macro_hygiene)]
#![allow(improper_ctypes)]
#![allow(improper_ctypes_definitions)]

use deko_core::cpu::gdt::GLOBAL_GDT;
use deko_core::cpu::idt::{create_early_idt, init_early_idt, Idt};
use deko_core::cpu::regs::{cr0_init, cr4_init, load_cr3, sse_init};
use deko_core::cpu::task::{DekoRunQueue, DekoRunQueuePred};
use deko_core::cpu::{DekoCpuCtx, DekoCpuCtxPermission, IST_DF, PERCPU_AREAS};
use deko_core::elf::ElfFile;
use deko_core::logging::print_banner;
use deko_core::mm::paging::{
    all_in_range_paddrs, bit_not_in_addr_region, bit_not_overlapping, index_at_level_spec,
    PageTable, PageTablePath, PageTablePermission, PteFlags, Pte_ALL_BITS, GLOBAL, RECURSIVE_INDEX,
};
use deko_core::mm::stack::{DekoIstStack, DekoKernelStack};
use deko_core::mm::vm::{VirtualMemory, VirtualMemoryPermission, VirtualMemoryRegion, VMR_GRANULE};
use deko_core::mm::{virt_to_phys, DEKO_FRAME_ALLOCATOR};
use deko_core::snp::ghcb::GuestHostCommucationBlock;
use deko_core::snp::logging::init_ghcb_logging;
use deko_core::snp::{init_guest_host, setup_apic};
use deko_core::{get_igvm_params, kinfo, DekoKernelLaunchInfo};
use deko_std::prelude::*;
use vstd::prelude::*;

core::arch::global_asm!(include_str!("../monitor.S"), options(att_syntax));

verus! {

axiom fn dummy_perm() -> tracked DekoCpuCtxPermission;

#[verus_spec(r =>
    with
        Tracked(pgtable_perm): Tracked<PageTablePermission>,
            -> cpu_perm: Tracked<DekoCpuCtxPermission>,
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
) -> DekoPPtr<DekoCpuCtx> {
    broadcast use PteFlags::lemma_each_bit_is_valid;
    broadcast use PteFlags::lemma_from_bits_single;
    broadcast use VirtAddr::lemma_page_size_eq_shifts;
    broadcast use VirtAddr::lemma_page_shift_le_max;
    broadcast use VirtAddr::lemma_pfn_roundtrip;

    let shared_area_ptr = {
        let read_handle = PERCPU_AREAS.acquire_read();
        // The permission is discarded; you can only obtain this permission
        // if you own this.
        let (ptr, _) = read_handle.borrow().data.0.index_as_ptr(0);

        read_handle.release_read();

        ptr
    };

    // We first allocate a new CPU context for the BSP.
    let (bsp_ctx_ptr, Tracked(ctx_perm)) = boxed_ptr!(DekoCpuCtx, &DEKO_FRAME_ALLOCATOR.0);
    let (ghcb, Tracked(ghch_perm)) = boxed_ptr!(GuestHostCommucationBlock, &DEKO_FRAME_ALLOCATOR.0);

    // Allocate a stack for performing the context switches,
    let (ctx_switch_stack, Tracked(stack_perm)) =
        boxed_ptr!(DekoKernelStack, &DEKO_FRAME_ALLOCATOR.0);
    let ctx_switch_stack_paddr = virt_to_phys(
        private_bit,
        shared_bit,
        ctx_switch_stack.into_vaddr(),
        Tracked(&pgtable_perm),
    );
    let (cpu_ist_stack, Tracked(ist_stack_perm)) =
        boxed_ptr!(DekoKernelStack, &DEKO_FRAME_ALLOCATOR.0);
    let cpu_ist_stack_paddr = virt_to_phys(
        private_bit,
        shared_bit,
        cpu_ist_stack.into_vaddr(),
        Tracked(&pgtable_perm),
    );

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
        assert(0xFFFFFF8000000000 as u64 % PAGE_SIZE == 0 && 0xFFFFFF0000000000 as u64 % PAGE_SIZE
            == 0) by (bit_vector);
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
        range: cpu_start..VirtAddr(cpu_start.0 + PAGE_SIZE),
        paddr,
        flags: cpu_self_flags,
    };

    proof {
        assert(vm_block_for_self.range.end@ % PAGE_SIZE == 0) by (compute);
        assert(index_at_level_spec(3, VirtAddr(0xFFFFFF0000000000)) != RECURSIVE_INDEX)
            by (compute);
        assert(index_at_level_spec(3, VirtAddr(0xFFFFFF0000001000)) != RECURSIVE_INDEX)
            by (compute);
        assert forall|vaddr: VirtAddr|
            #![auto]
            vm_block_for_self.range.start@ <= vaddr@ < vm_block_for_self.range.end@ && vaddr@
                % PAGE_SIZE == 0 ==> {
                &&& PageTablePath::from_vaddr(vaddr).is_normalized()
                &&& PageTablePath::from_vaddr(vaddr).wf()
            } by {
            broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        };

        // Currently we do not have a good way for reasoning about this so
        // mark these two assumptions here.
        assume(paddr@ + PAGE_SIZE < 0x000f_ffff_ffff_f000);
        assume(all_in_range_paddrs(&vm_region.ms, paddr, vm_block_for_self.range));
    }

    let tracked vm_block_for_cpu_perm = VirtualMemoryPermission {
        parent_id: vm_region.id@,
        range: cpu_start..VirtAddr((cpu_start.0 + PAGE_SIZE) as u64),
    };

    // There are some proofs. Insert into the region.
    proof_with!(Tracked(&mut vm_perm), Tracked(vm_block_for_cpu_perm));
    vm_region.insert(vm_block_for_self);

    let cpu_stack = DekoKernelStack::new_with_size(0x8000, false);
    let top_of_the_stack = VirtAddr(cpu_stack.stack_top() + CONTEXT_SWITCH_STACK.0);
    // Create a new vm_block for the stack and then map it.
    let vm_block_for_stack = VirtualMemory {
        range: VirtAddr(top_of_the_stack.0 - 0x8000)..top_of_the_stack,
        paddr: ctx_switch_stack_paddr,
        flags: PteFlags::nx_kernel(),
    };

    let tracked vm_block_for_stack_perm = VirtualMemoryPermission {
        parent_id: vm_region.id@,
        range: VirtAddr((top_of_the_stack.0 - 0x8000) as u64)..top_of_the_stack,
    };

    ctx_switch_stack.write(Tracked(&mut stack_perm), cpu_stack);

    proof {
        assume(vm_block_for_stack.wf());
        // The same proofs.
        assume(vm_region.compatible_spec(&vm_block_for_stack));
        assume(vm_region.disjoint_blocks(&vm_block_for_stack));
    }
    proof_with!(Tracked(&mut vm_perm), Tracked(vm_block_for_stack_perm));
    vm_region.insert(vm_block_for_stack);

    // Allocate a stack for interrupt service routines.
    let ist_df_stack = DekoKernelStack::new_with_size(0x8000, false);
    let top_of_ist_stack = VirtAddr(ist_df_stack.stack_top() + STACK_IST_DF_BASE.0);
    let vm_block_for_ist_stack = VirtualMemory {
        range: VirtAddr(top_of_ist_stack.0 - 0x8000)..top_of_ist_stack,
        paddr: cpu_ist_stack_paddr,
        flags: PteFlags::nx_kernel(),
    };
    let tracked vm_block_for_ist_stack_perm = VirtualMemoryPermission {
        parent_id: vm_region.id@,
        range: VirtAddr((top_of_ist_stack.0 - 0x8000) as u64)..top_of_ist_stack,
    };
    cpu_ist_stack.write(Tracked(&mut ist_stack_perm), ist_df_stack);
    proof {
        assume(vm_block_for_ist_stack.wf());
        // The same proofs.
        assume(vm_region.compatible_spec(&vm_block_for_ist_stack));
        assume(vm_region.disjoint_blocks(&vm_block_for_ist_stack));
    }

    proof_with!(Tracked(&mut vm_perm), Tracked(vm_block_for_ist_stack_perm));
    vm_region.insert(vm_block_for_ist_stack);

    let cpu_ist_stack = DekoIstStack { df_stack: Some(cpu_ist_stack), df_ss: None };
    let (run_queue, Tracked(run_queue_perm)) = DekoRunQueue::new();
    let run_queue = DekoRwLock::new(
        DekoAtomicData::new_with(run_queue, Tracked(run_queue_perm)),
        (),
        Ghost(DekoRunQueuePred {  }),
    );

    let cpu_ctx = DekoCpuCtx::new(
        init_pgtable,
        shared_area_ptr,
        ghcb,
        0,
        shared_bit,
        private_bit,
        kernel_mapping,
        Some(vm_region),
        Some(ctx_switch_stack),
        Some(cpu_ist_stack),
        Some(run_queue),
    );

    cpu_ctx.set_ist_stack_tss(IST_DF, top_of_ist_stack);

    // Finally we write the CPU context to the memory.
    bsp_ctx_ptr.write(Tracked(&mut ctx_perm), cpu_ctx);

    // let cpu_ctx_perm = Tracked(DekoCpuCtxPermission {
    //     ptr_perm: ctx_perm,
    //     pgtable_perm: dummy_pgtable_perm(),
    //     ghcb_perm: ghch_perm,
    //     ctx_switch_stack_perm: Some(stack_perm),
    //     vm_region_perm: Some(vm_perm),
    // });
    let tracked cpu_ctx_perm = dummy_perm();

    proof_with!(|= Tracked(cpu_ctx_perm));
    bsp_ctx_ptr
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

    proof_with!(Tracked(&mut ctx_perm));
    let (new_page_table, paddr, Tracked(pgtable_perm)) = deko_core::mm::paging::init_monitor_paging(
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

    // Prepare the BSP CPU context.
    proof_with!(Tracked(pgtable_perm) => Tracked(cpu_ctx_perm));
    let bst_cpu_ptr = setup_bsp_cpu(new_page_table, private_bit, shared_bit, ms);

    proof {
        // do it later.
        assume(cpu_ctx_perm.wf_with(bst_cpu_ptr));
        assume(cpu_ctx_perm.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf());
    }

    init_guest_host(bst_cpu_ptr, Tracked(&mut cpu_ctx_perm));

    init_ghcb_logging(debug_serial_port);
    print_banner();

    setup_apic(bst_cpu_ptr, Tracked(&mut cpu_ctx_perm));

    sse_init();
    proof {
        // do it later.
        assume(cpu_ctx_perm.wf_with(bst_cpu_ptr));
        assume(cpu_ctx_perm.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf());
    }
    // Assign "deko_main" to the BSP CPU context so that it will
    // start executing from there.
    DekoCpuCtx::setup_idle_task(bst_cpu_ptr, Tracked(&mut cpu_ctx_perm), 114514);

    loop {
        // should never reach here
        // early_die();
    }
    // deko_core::hal::setup_env(ctx);
}

/// The "main" function scheduled after the monitor is fully set up.
fn deko_main() {
}

#[verifier::external]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    // Print detailed panic information using the logging system
    #[cfg(feature = "logging")]
    deko_core::logging::print_panic_info(info);

    loop {
    }
}

} // verus!
