#![no_std]
#![no_main]
#![feature(proc_macro_hygiene)]
#![feature(likely_unlikely)]
#![allow(improper_ctypes)]
#![allow(improper_ctypes_definitions)]

use core::ptr::eq;

use deko_core::collections::get_unchecked;
use deko_core::cpu::gdt::GLOBAL_GDT;
use deko_core::cpu::idt::{create_early_idt, init_early_idt, init_global_idt, Idt};
use deko_core::cpu::regs::{cr0_init, cr4_init, load_cr3, sse_init};
use deko_core::cpu::task::{
    self, cpu_idle, run_kernel_tasks, schedule_init, DekoRunQueue, DekoRunQueuePred, DekoRunnable,
};
use deko_core::cpu::{
    set_availabe_cpu_nums, start_application_processor, CpuidTable, DekoCpuCtx,
    DekoCpuCtxPermission, PerCpuShared, CPUID_MAX_COUNT, IST_DF, PERCPU_AREAS,
};
use deko_core::elf::ElfFile;
use deko_core::fs::ramfs::init_ramfs;
use deko_core::fw::{load_acpi_tables, read_acpi_table};
use deko_core::hal::set_is_stage2;
use deko_core::logging::print_banner;
use deko_core::mm::frame_allocator::DekoAllocatorApi;
use deko_core::mm::paging::{
    all_in_range_paddrs, bit_not_in_addr_region, bit_not_overlapping, index_at_level_spec,
    PageTable, PageTablePath, PageTablePermission, PteFlags, Pte_ALL_BITS, GLOBAL, RECURSIVE_INDEX,
};
use deko_core::mm::stack::{DekoIstStack, DekoKernelStack};
use deko_core::mm::vm::{
    VirtualMemory, VirtualMemoryPermission, VirtualMemoryRegion, VmMapping, VmMappingPred,
    VMR_GRANULE,
};
use deko_core::mm::{virt_to_phys, DEKO_FRAME_ALLOCATOR_FULL};
use deko_core::snp::ghcb::GuestHostCommunicationBlock;
use deko_core::snp::logging::init_ghcb_logging;
use deko_core::snp::req::init_snp_guest_driver;
use deko_core::snp::{init_guest_host, init_secrets_page, prepare_guest_fw, setup_apic};
use deko_core::{
    dbg, die, get_igvm_params, kdebug, kerror, kinfo, kpanic_if, kwarn, DekoKernelLaunchInfo,
};
use deko_std::prelude::*;
use vstd::prelude::*;

core::arch::global_asm!(include_str!("../monitor.S"), options(att_syntax));

verus! {

// TODO: Replace the real thing.
axiom fn dummy_perm() -> tracked DekoCpuCtxPermission;

struct DekoKernelLaunchInfoPred;

impl Predicate<DekoAtomicData<DekoKernelLaunchInfo, ()>> for DekoKernelLaunchInfoPred {
    open spec fn inv(self, data: DekoAtomicData<DekoKernelLaunchInfo, ()>) -> bool {
        data.wf()
    }
}

/// Populated later.
exec static LAUNCH_INFO: DekoOnceCell<DekoKernelLaunchInfo, (), DekoKernelLaunchInfoPred>
    ensures
        LAUNCH_INFO.wf(),
{
    DekoOnceCell::new(Ghost(DekoKernelLaunchInfoPred {  }))
}

exec static CPUID_PAGE: DekoSimpleOnceCell<CpuidTable>
    ensures
        CPUID_PAGE.wf(),
{
    DekoSimpleOnceCell::new(Ghost(()))
}

#[verifier::external_body]
#[verus_spec(
    with
        Tracked(ctx_perm): Tracked<&DekoCpuCtxPermission>,
    requires
        addr.wf(),
        ctx_perm.pgtable_perm.mapped(addr),
)]
fn init_cpuid_table(addr: VirtAddr) {
    let cpuid_tables = unsafe { &mut *(addr.0 as *mut CpuidTable) };

    for fns in cpuid_tables.func.0.iter_mut() {
        if fns.eax_in == 0x8000_001f {
            fns.eax_out |= 1 << 28;
        }
    }

    CPUID_PAGE.init(cpuid_tables.clone());
}

/// Starts all application processors.
#[verus_spec(
    requires
        igvm_params.wf(),
)]
fn start_application_processors(igvm_params: &IgvmParams<'_>) {
    kinfo!("igvm_params.madt_data", igvm_params.igvm_madt);

    // CPU topology can be either from IGVM MADT or from firmware ACPI tables, but
    // we try to read it from IGVM MADT first.
    if let Some(cpus) = igvm_params.load_cpu_info(DekoAllocatorApi {  }) {
        kinfo!("CPU topology:", cpus);
    } else {
        kinfo!("No CPU info found in IGVM parameters; trying firmware ACPI tables");

        // do probe from firmware ACPI tables.
        let Some(acpi_fw) = load_acpi_tables() else {
            kwarn!("No ACPI tables found in firmware; no APs will be started");
            return ;
        };

        let mut i = 0;

        while i < acpi_fw.tables.len()
            invariant
                0 <= i <= acpi_fw.tables@.len(),
                acpi_fw.tables.wf(),
            decreases acpi_fw.tables@.len() - i,
        {
            let table_meta = acpi_fw.tables.index(i);

            assume(forall|i: int| 0 <= i < 4 ==> 0 <= #[trigger] table_meta.sig@[i] < 128);

            if <str as PartialEq>::eq(table_meta.sig.as_str(), "APIC") {
                kdebug!("Found APIC table in ACPI tables at offset", table_meta.offset);

                break ;
            }
            i += 1;
        }

        if i >= acpi_fw.tables.len() {
            kwarn!("No APIC table found in ACPI tables; no APs will be started");
            return ;
        }
        let offset = acpi_fw.tables.index(i).offset;
        let Some(apic_table) = read_acpi_table(&acpi_fw.buf, offset) else {
            kwarn!("Failed to read APIC table; no APs will be started");
            return ;
        };

        // Now we parse the content.
        let Some(cpus) = apic_table.get_cpu_topology(DekoAllocatorApi {  }) else {
            kwarn!("No CPU info found in APIC table; no APs will be started");
            return ;
        };

        kpanic_if!(
            core::hint::unlikely(cpus.len() == 0 || cpus.len() > CPUID_MAX_COUNT as usize),
            "Invalid CPU count from ACPI APIC table:", cpus.len()
        );

        set_availabe_cpu_nums(cpus.len() as u64);

        do_make_ap_online(&cpus);
    }
}

/// This function is split from `start_application_processors` to prevent
/// stack overflow since we only allocated a small stack for the monitor.
///
/// Seems we do not have a good way to control the proper usage of stack
/// sizes so the best practice is to restrict large stack usage functions to
/// be separate functions.
#[verifier::exec_allows_no_decreases_clause]
fn do_make_ap_online(cpus: &[ACPICPUInfo]) {
    let mut i = 1;  // BSP is already up.
    #[verus_spec(
            invariant
                1 <= i <= cpus.len() + 1,
            decreases cpus@.len() - i,
        )]
    while i < cpus.len() {
        let cpu_info = &cpus[i];
        kpanic_if!(
                core::hint::unlikely(cpu_info.apic_id >= CPUID_MAX_COUNT as u32),
                "CPU is exceeds maximum:",
                cpu_info.apic_id,
                CPUID_MAX_COUNT
            );

        deko_rwlock_read_atomic_data! {
            PERCPU_AREAS,
            percpu_area,
            __,
            {
                let Some(ref percpu_area) = percpu_area else {
                    die("PERCPU_AREAS is not initialized");
                };

                kpanic_if!(
                    core::hint::unlikely(cpu_info.apic_id as usize >= percpu_area.0.len()),
                    "AP CPU ID out of bounds in per-CPU shared area: got;", cpu_info.apic_id
                );

                start_application_processor(get_unchecked(&percpu_area.0, cpu_info.apic_id as usize));
            }
        }

        // Wait for the CPU to be online.
        loop
            invariant
                cpu_info.apic_id < CPUID_MAX_COUNT as u32,
        {
            core::hint::spin_loop();

            let is_online =
                deko_rwlock_read_atomic_data! {
                PERCPU_AREAS,
                percpu_area,
                percpu_area_perm,
                {
                    let Some(ref percpu_area) = percpu_area else {
                        die("PERCPU_AREAS is not initialized");
                    };

                    kpanic_if!(
                        core::hint::unlikely(cpu_info.apic_id as usize >= percpu_area.0.len()),
                        "AP CPU ID out of bounds in per-CPU shared area: got;", cpu_info.apic_id
                    );

                    let cpu_area = &percpu_area.0[cpu_info.apic_id as usize];
                    let tracked this_perm = percpu_area_perm.borrow().shared_perms.tracked_borrow(
                        cpu_info.apic_id as int,
                    );

                    cpu_area.online.load(Tracked(&this_perm.online_perm))
                }
            };

            if is_online {
                break ;
            }
        }

        i += 1;
    }
}

#[inline]
#[verus_spec(r =>
    requires
        header.wf(),
)]
fn init_mem(header: &DekoKernelLaunchInfo) {
    let heap_start = header.heap_area_virt_start;
    let heap_size = header.heap_area_size;

    DEKO_FRAME_ALLOCATOR_FULL.init(heap_start, heap_size);
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
        ctx_perm.pgtable_perm.mapped(VirtAddr(header.secrets_page)),
        ctx_perm.pgtable_perm.mapped(VirtAddr(header.cpuid_page)),
        VirtAddr(header.secrets_page).wf(),
        VirtAddr(header.cpuid_page).wf(),
        ctx_perm.wf_with(ctx),
        header.wf(),
)]
extern "C" fn deko_entry(ctx: DekoPPtr<DekoCpuCtx>, header: &DekoKernelLaunchInfo) -> ! {
    set_is_stage2(false);

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
        ctx_perm.pgtable_perm.mapped(VirtAddr(header.secrets_page)),
        ctx_perm.pgtable_perm.mapped(VirtAddr(header.cpuid_page)),
        VirtAddr(header.secrets_page).wf(),
        VirtAddr(header.cpuid_page).wf(),
        header.wf(),
)]
fn deko_setup(ctx: DekoPPtr<DekoCpuCtx>, header: &DekoKernelLaunchInfo) -> ! {
    LAUNCH_INFO.init(DekoAtomicData::new(header.clone()));

    GLOBAL_GDT.load_selectors();

    let mut early_idt = Idt { entries: create_early_idt() };
    init_early_idt(&mut early_idt);

    proof_with!(Tracked(&ctx_perm));
    init_cpuid_table(VirtAddr(header.cpuid_page));

    proof_with!(Tracked(&ctx_perm));
    deko_core::imp::init_secrets_page(VirtAddr(header.secrets_page));

    let debug_serial_port = header.debug_serial_port;
    let secrets_page_virt = VirtAddr(header.secrets_page);

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
    // buggy.
    let bsp_cpu_ptr = DekoCpuCtx::setup_cpu(
        new_page_table,
        private_bit,
        shared_bit,
        ms,
        0,
        &DEKO_FRAME_ALLOCATOR_FULL,
    );

    proof {
        // do it later.
        assume(cpu_ctx_perm.wf_with(bsp_cpu_ptr));
        assume(cpu_ctx_perm.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf());
    }

    init_guest_host(bsp_cpu_ptr, Tracked(&mut cpu_ctx_perm));

    init_ghcb_logging(debug_serial_port);
    print_banner();

    kinfo!("The remaining memory in frame allocator:",
        DEKO_FRAME_ALLOCATOR_FULL.0.remaining(),
    );

    setup_apic(bsp_cpu_ptr, Tracked(&mut cpu_ctx_perm));

    init_global_idt();

    sse_init();
    proof {
        // do it later.
        assume(cpu_ctx_perm.wf_with(bsp_cpu_ptr));
        assume(cpu_ctx_perm.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf());
        assume(cpu_ctx_perm.ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf());
    }

    // Assign "deko_main" to the BSP CPU context so that it will
    // start executing from there.
    proof_with!(Tracked(cpu_ctx_perm) => Tracked(cpu_ctx_perm));
    DekoCpuCtx::setup_idle_task(bsp_cpu_ptr, deko_main_func_ptr(), "deko_main");

    unsafe {
        schedule_init();
    }

    // This is unreachable; if this function gets called then
    // `schedule_init` must have failed.
    kerror!("deko_setup: reached unreachable point");
    early_die();
}

/// The "main" function scheduled after the monitor is fully set up.
#[verifier::exec_allows_no_decreases_clause]
#[verus_spec(
    with
        Tracked(cpu_ctx_perm): Tracked<DekoCpuCtxPermission>,
    requires
        cpu_ctx_perm.wf(),
        cpu_ctx_perm.ptr_perm.value().cpu_id() == 0,
        cpu_index == cpu_ctx_perm.ptr_perm.value().cpu_id(),
        cpu_ctx_perm.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
        cpu_ctx_perm.ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf(),
)]
fn deko_main(cpu_index: usize) {
    kinfo!("deko_main: entered");

    if let Some(DekoAtomicData { data: launch_info, .. }) = LAUNCH_INFO.get() {
        let (this_cpu, _) = DekoCpuCtx::this_cpu();
        let tracked mut cpu_ctx_perm = cpu_ctx_perm;
        let igvm_addr = VirtAddr::new(launch_info.igvm_params_virt_addr as u64);

        assume(cpu_ctx_perm.pgtable_perm.mapped(igvm_addr));
        assume(cpu_ctx_perm.wf_with(this_cpu));

        proof_with!(Tracked(&cpu_ctx_perm));
        let igvm_params = deko_core::get_igvm_params(igvm_addr);

        let kernel_prange = PaddrRange {
            start: PhysAddr(launch_info.kernel_region_phys_start),
            end: PhysAddr(launch_info.kernel_region_phys_end),
        };

        assume(kernel_prange.wf());

        let Some(cpuid_table) = CPUID_PAGE.get() else {
            kerror!("deko_main: CPUID page not initialized; this is a fatal error");
            early_die();
        };

        proof_with!(Tracked(&mut cpu_ctx_perm.pgtable_perm));
        deko_core::fw::invalidate_early_boot_mem(launch_info, &igvm_params);

        start_application_processors(&igvm_params);

        proof_with!(Tracked(&mut cpu_ctx_perm.pgtable_perm));
        deko_core::imp::prepare_guest_fw(launch_info, &igvm_params, kernel_prange, cpuid_table);

        // Populate the rootfs.
        init_ramfs(PhysAddr(launch_info.kernel_fs_start)..PhysAddr(launch_info.kernel_fs_end));

        // Initialize the guest driver.
        init_snp_guest_driver();

        proof_with!(Tracked(cpu_ctx_perm) => Tracked(mut new_perm));
        let serv_task = DekoRunnable::new(
            this_cpu,
            task::DekoTaskArgs {
                parent: None,
                entry: task::serv_main_func_ptr(),
                name: "serv_main",
                mode: task::DekoTaskMode::Kernel {
                    entry: task::serv_main_func_ptr(),
                    param: 0,
                    ret: task::run_kernel_tasks_func_ptr(),
                },
            },
        );

        DekoCpuCtx::start_kernel_task(this_cpu, Tracked(&mut new_perm), serv_task);  // schedule now

        cpu_idle(cpu_index);  // guard in case schedule fails
    } else {
        kerror!("deko_main: launch info not initialized");
        early_die();
    }
}

func_ptr!(deko_main);

#[verifier::external]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    // Print detailed panic information using the logging system
    #[cfg(feature = "logging")]
    deko_core::logging::print_panic_info(info);

    dbg::print_stack(3);

    unsafe {
        core::arch::asm!("ud2");
    }

    loop {
    }
}

} // verus!
