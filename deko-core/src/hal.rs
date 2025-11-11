use core::sync::atomic::{AtomicBool, Ordering};

use deko_std::prelude::*;
use vstd::prelude::*;

use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::gdt::GlobalDescriptorTable;
use crate::cpu::idt::{
    create_early_idt, stage2_generic_idt_handler, stage2_generic_idt_handler_no_ghcb, Idt,
};
use crate::cpu::{register_cpuid_table, DekoCpuCtx, DekoCpuCtxPermission};
use crate::elf::{ElfFile, ElfLoadSegment};
use crate::mm::{init_frame_allocator, DEKO_MAPPING_SPACE};
use crate::snp::get_igvm_params_block;
use crate::{die, imp, kerror, kinfo, Stage2LaunchInfo};

verus! {

/// A global flag to indicate whether the AP has been started.
///
/// Allow APs to proceed as the environment is now ready. This
/// is set by the BSP after all initialization is done.
#[no_mangle]
#[link_section = ".ap_section"]
pub exec static AP_FLAG: AtomicBool = AtomicBool::new(false);

#[verifier::external_body]
#[inline(always)]
fn allow_ap_to_proceed() {
    AP_FLAG.store(true, Ordering::Release);
}

#[derive(PartialEq, Eq)]
pub enum PlatformType {
    Snp,
    Tdx,
    None,  // not supported yet.
}

impl WellFormed for PlatformType {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl From<u32> for PlatformType {
    fn from(value: u32) -> (r: Self)
        ensures
            match value {
                0x0001 => r == PlatformType::Snp,
                0x0002 => r == PlatformType::Tdx,
                _ => r == PlatformType::None,
            },
    {
        match value {
            0x0001 => PlatformType::Snp,
            0x0002 => PlatformType::Tdx,
            _ => PlatformType::None,
        }
    }
}

impl Clone for PlatformType {
    fn clone(&self) -> (r: Self)
        ensures
            (r == *self),
    {
        match self {
            Self::Snp => Self::Snp,
            Self::Tdx => Self::Tdx,
            Self::None => Self::None,
        }
    }
}

pub struct PlatformPredicate;

impl Predicate<PlatformType> for PlatformPredicate {
    open spec fn inv(self, platform_type: PlatformType) -> bool {
        match platform_type {
            PlatformType::Tdx | PlatformType::Snp => true,
            _ => false,
        }
    }
}

/// A global platform type that is initialized once at system startup.
///
/// This static variable holds the detected platform type (SNP or TDX) and is designed
/// to be initialized by the BSP (Bootstrap Processor) during early boot, then accessed
/// by all cores throughout the system's lifetime.
///
/// # Verification Limitations
///
/// Verus currently has limited support for reasoning about static variables:
///
/// 1. **No spec method access**: We cannot invoke any of the static's `spec` methods
///    in specifications, preventing us from writing preconditions like
///    `requires PLATFORM.is_init()`.
///
/// 2. **No ghost state visibility**: The ghost state tracking initialization status
///    is tied to the atomic value and cannot be observed in pure spec code.
///
/// 3. **No cross-core reasoning**: Verus cannot verify that the BSP initializes this
///    variable before APs (Application Processors) access it, even though our boot
///    protocol guarantees this ordering.
///
/// # Safety Invariants (Runtime-Guaranteed, Not Verus-Verified)
///
/// The following invariants are maintained by our boot protocol and hardware behavior,
/// but cannot be formally verified in Verus:
///
/// 1. **Initialization Ordering**: The BSP executes initialization code before any AP
///    begins execution. This is guaranteed by hardware (APs start in wait-for-SIPI state)
///    and our bootloader (which sends SIPI only after BSP initialization).
///
/// 2. **Single Initialization**: The platform type is set exactly once by the BSP.
///    The `OnceLock` ensures atomicity, preventing race conditions if multiple cores
///    somehow attempt initialization.
///
/// 3. **Availability Guarantee**: When any AP code runs, `PLATFORM.get().is_some()`
///    is guaranteed to be true.
///
/// # Why a Static Variable?
///
/// Alternative designs were considered but rejected:
///
/// - **Passing platform type as parameter**: Would require threading this value through
///   every function call in the system, cluttering APIs and complicating the codebase.
///
/// - **Per-core storage**: Would require complex synchronization to ensure consistency
///   and waste memory storing identical values.
///
/// - **Const generic parameter**: Would require compile-time knowledge of platform type,
///   but this is only determined at runtime through CPUID detection.
///
/// # Verification Workarounds
///
/// Since we cannot directly verify properties of this static, we employ several strategies:
///
/// ## 1. Trusted Wrapper Functions
/// ```ignore
/// #[verifier::external_body]
/// pub fn get_platform() -> PlatformType {
///     PLATFORM.get().expect("Platform not initialized")
/// }
/// ```
///
/// ## 2. Ghost Tokens (Considered but not implemented)
/// We considered maintaining a parallel `tracked` variable that shadows the static:
/// ```ignore
/// tracked static PLATFORM_INIT_TOKEN: Option<InitToken>;
/// ```
/// However, this approach has its own limitations as we still cannot connect the ghost
/// token to the actual initialization state in specifications.
///
/// ## 3. Defensive Runtime Checks
/// In debug builds, we validate our assumptions:
/// ```ignore
/// debug_assert!(PLATFORM.get().is_some(), "Platform accessed before initialization");
/// ```
///
/// # Usage Example
///
/// ```ignore
/// // In BSP initialization code (runs first)
/// pub fn bsp_init() {
///     let platform_type = detect_platform_type();  // SNP or TDX
///     PLATFORM.init_or_panic(platform_type, "Failed to initialize platform type");
///     // ... start APs ...
/// }
///
/// // In AP entry point (called from assembly after BSP initialization)
/// #[verifier::external_body]  // Cannot verify assembly-to-Rust transition
/// pub fn ap_main() {
///     // Safe to unwrap: BSP guaranteed to have initialized
///     let platform = PLATFORM.get().unwrap();
///     // ... use platform ...
/// }
/// ```
///
/// # Trust Boundary
///
/// This static variable represents a trust boundary in our verification:
/// - **Below this layer**: Hardware, firmware, and assembly code ensure proper ordering
/// - **At this layer**: We trust that initialization has occurred when accessed
/// - **Above this layer**: Verified Rust code can safely use the platform type
///
/// This is a fundamental limitation when verifying systems code: some guarantees come
/// from outside the verified language's model and must be explicitly trusted.
pub exec static PLATFORM: OnceLock<PlatformType, PlatformPredicate>
    ensures
        PLATFORM.wf(),
{
    OnceLock::new(Ghost(PlatformPredicate {  }))
}

/// Injects dummy handlers into the IDT so that we can do early-stage
/// exception handling (although this does nothing for now).
#[inline(always)]
#[verus_spec(r =>
    requires
        old(idt).entries.wf(),
    ensures
        idt.wf(),
)]
fn init_early_idt(idt: &mut Idt) {
    crate::cpu::idt::init_early_idt(idt);
}

#[inline(always)]
#[verus_spec(r =>
    requires
        old(idt).wf(),
    ensures
        idt.wf(),
)]
fn init_early_idt_late(idt: &mut Idt) {
    crate::cpu::idt::init_generic_idt(idt);
}

/// Sets up the environment for the platform which will setup the GDT, kernel mapping, paging,
/// kernel loading, heaps, etc.
#[verifier::exec_allows_no_decreases_clause]
#[verus_spec(__ =>
    requires
        ctx_perm@.wf_with(ctx),
        ctx_perm@.current_cpu_core.is_bsp(),
    ensures
)]
pub fn setup_env(ctx: DekoPPtr<DekoCtx>, ctx_perm: Tracked<DekoCtxPermission>) -> (__discard: !) {
    let Tracked(mut ctx_perm) = ctx_perm;

    // Extract the launch info from the context.
    let header = ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).stage2_launch_info.borrow(
        Tracked(&ctx_perm.stage2_launch_info_perm),
    ).clone();

    // Set up the GDT.
    GlobalDescriptorTable::init_gdt(Tracked(&ctx_perm.current_cpu_core));

    let platform_type = PlatformType::from(header.platform_type);
    PLATFORM.init(platform_type.clone());

    // Initialize the IDT.
    let mut idt = Idt { entries: create_early_idt() };
    init_early_idt(&mut idt);

    // Do some platform-specific stuff.
    imp::init_platform(header);

    // TODO: Register the CPUID table: so that we know cpuids of each core.
    unsafe {
        register_cpuid_table(header.cpuid_page);
    }

    // Set up the kernel mapping: now identity
    // an automatic invariant for OnceCell.
    let virt_start = VirtAddr::from(STAGE2_START as u64);
    let virt_end = VirtAddr::from(header.stage2_end as u64);
    let phys_start = PhysAddr::from(STAGE2_START as u64);
    let kernel_mapping = FixedAddressMappingRange::new(virt_start, virt_end, phys_start);

    // SVSM ref: Create a simple heap mapping using the lower memory region.
    let zero = VirtAddr::from(0u64);
    let lowmem = VirtAddr::from(LOWMEM_END as u64);
    let heap_mapping = FixedAddressMappingRange::new(zero, lowmem, PhysAddr::from(0u64));

    imp::validate_memory(Tracked(&mut ctx_perm), 0, LOWMEM_END as u64);

    assert(ctx_perm.wf());

    let mapping_space = MappingSpace { kernel: kernel_mapping, physmap: heap_mapping };
    DEKO_MAPPING_SPACE.init(mapping_space);

    // BSP done; allow APs to proceed.
    allow_ap_to_proceed();

    // Initialize the heap (physical memory region).
    let heap_start = VirtAddr::from(STAGE2_HEAP_START as u64);
    let heap_end = VirtAddr::from(STAGE2_HEAP_END as u64);
    proof {
        crate::proof::stage2_heap_valid_params();

        assert(heap_start.wf());
        assert(heap_end.wf());

        let heap_start_val = heap_start@;
    }

    init_frame_allocator(&heap_start, &heap_end);

    // Initialize per-cpu-specific structures.
    let ctx_perm = Tracked(ctx_perm);
    let (ctx, Tracked(mut ctx_perm)) = imp::init_each_cpu(ctx, ctx_perm);

    init_early_idt_late(&mut idt);

    let igvm_params_block = get_igvm_params_block(&header);
    imp::init_platform_end(&igvm_params_block, Tracked(&mut ctx_perm));

    // now we need to load the kernel into the memory.
    // first we need to find where it is.
    if let Some((kernel_phys_start, kernel_phys_end)) = igvm_params_block.find_kernel_region() {
        kinfo!("Deko found the kernel physical range:  [",
                kernel_phys_start.0 => hex, " - ", kernel_phys_end.0 => hex, "]");
        kinfo!("Loading the Deko monitor...");

        let mut loaded_kernel_end = kernel_phys_start;

        // Load the ELF file.
        if let Some((entry, mut loaded_kernel_vregion)) = #[verus_spec(with Tracked(&mut ctx_perm))]
        load_deko_monitor(ctx, &mut loaded_kernel_end, header) {
            kinfo!("Deko monitor loaded successfully!");
            kinfo!("Kernel virtual range:", loaded_kernel_vregion);
            kinfo!("Kernel entry point at: ", entry.0 => hex,);

            let mut loaded_kernel_pregion = kernel_phys_start..loaded_kernel_end;

            kinfo!("Loaded kernel physical range:", loaded_kernel_pregion);

            if core::intrinsics::unlikely(loaded_kernel_end.0 > kernel_phys_end.0) {
                crate::die("Deko monitor loading exceeded the allocated kernel physical region!");
            }
            // Load the IGVM params, if present. Update loaded region accordingly.
            // SAFETY: The loaded kernel region was correctly calculated above and
            // is sized appropriately to include a copy of the IGVM parameters.

            proof {
                // FIXME: Do it later because we have not (yet) proved
                // that the mapped region for this will not change
                // throughout previous operations.
                assume(ctx_perm.pgtable_perm.mapped(VirtAddr::new(header.igvm_params as u64)));
            }
            let igvm_params = #[verus_spec(with Tracked(&ctx_perm))]
            header.get_igvm_params();
            let (igvm_vregion, igvm_pregion) = #[verus_spec(with Tracked(&mut ctx_perm))]
            load_igvm_params(
                ctx,
                header,
                &igvm_params,
                loaded_kernel_vregion,
                loaded_kernel_pregion,
            );

            kinfo!("IGVM params virtual range:", igvm_vregion);
            kinfo!("IGVM params physical range:", igvm_pregion);
        } else {
            kerror!("Deko failed to load the kernel ELF file! Check if the format is correct.");
        }
    } else {
        kerror!("Deko failed to find the kernel physical range from the boot header!");
    }

    loop {
    }
}

/// Loads the IGVM params at the next contiguous location from the loaded
/// kernel image. Returns the virtual and physical memory regions hosting the
/// loaded data.
#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>
    requires
        old(ctx_perm).wf_with(ctx),
        header.wf_for_loading(old(ctx_perm).pgtable_perm.mapping_space),
        igvm_params.wf(),
        loaded_kernel_vregion.wf(),
        loaded_kernel_pregion.wf(),
        loaded_kernel_vregion.end@ >= VADDR_UPPER_MASK,
        loaded_kernel_pregion.start@ % PAGE_SIZE == 0,
        loaded_kernel_pregion.end@ % PAGE_SIZE == 0,
        loaded_kernel_vregion.start@ % PAGE_SIZE == 0,
        loaded_kernel_vregion.end@ % PAGE_SIZE == 0,
    ensures
        r.0.wf(),
        r.1.wf(),
)]
fn load_igvm_params(
    ctx: DekoPPtr<DekoCpuCtx>,
    header: Stage2LaunchInfo,
    igvm_params: &IgvmParams,
    loaded_kernel_vregion: VaddrRange,
    loaded_kernel_pregion: PaddrRange,
) -> (r: (VaddrRange, PaddrRange)) {
    let param_size = igvm_params.size();

    kinfo!("Loading IGVM params of size: ", param_size => hex, " bytes");

    proof {
        // TODO: The spec for these is non-trivial; we
        // leave them as assumptions for now and will
        // revisit later.
        //
        // This actually needs us to say:
        // loaded_kernel_vregion.end == loaded_so_far(header)
        assume(loaded_kernel_vregion.end@ + param_size <= u64::MAX);
        assume(loaded_kernel_pregion.end@ + param_size <= u64::MAX);

        assert((loaded_kernel_vregion.end@ + param_size as u64) % PAGE_SIZE as int == 0) by {
            assert(loaded_kernel_vregion.end@ % PAGE_SIZE == 0);
            assert(param_size as u64 % PAGE_SIZE == 0);
            vstd::arithmetic::div_mod::lemma_mod_adds(
                loaded_kernel_vregion.end@ as int,
                param_size as int,
                PAGE_SIZE as int,
            );
        }
    }

    let igvm_vregion_end = loaded_kernel_vregion.end.0 + param_size as u64;
    let igvm_pregion_end = loaded_kernel_pregion.end.0 + param_size as u64;

    let igvm_vregion = loaded_kernel_vregion.end..VirtAddr(igvm_vregion_end);
    let igvm_pregion = loaded_kernel_pregion.end..PhysAddr(igvm_pregion_end);

    proof {
        // Similar to above, we leave these as
        // assumptions for now.
        // loaded_kernel_vregion.end == loaded_so_far(header)
        // just need some extra utility to bridge them together.
        assume(param_size + igvm_pregion_end < 0x000f_ffff_ffff_f000);
    }

    #[verus_spec(with Tracked(ctx_perm))]
    crate::mm::paging::map_and_validate(
        ctx,
        header,
        igvm_vregion.start,
        igvm_vregion.end,
        igvm_pregion.start,
    );

    crate::die("Not implemented yet");
}

/// Loads the kernel ELF and returns the virtual memory region where it
/// resides, as well as its entry point. Updates the used physical memory
/// region accordingly.
#[verifier::spinoff_prover]
#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>
    requires
        old(ctx_perm).wf_with(ctx),
        old(kernel_end).wf(),
        old(kernel_end)@ % PAGE_SIZE == 0,
        header.wf_for_loading(old(ctx_perm).pgtable_perm.mapping_space),
        header.get_igvm_param_block_spec().find_kernel_region_spec() matches Some((kstart, _)) ==> kstart == old(kernel_end),
    ensures
        ctx_perm.wf_with(ctx),
        ctx_perm.pgtable_perm.mapping_space == old(ctx_perm).pgtable_perm.mapping_space,
        r matches Some((entry_point, vaddr_range))
            ==> {
                    &&& entry_point.wf()
                    &&& vaddr_range.wf()
                    &&& kernel_end.wf()
                    &&& kernel_end@ > old(kernel_end)@
                    &&& kernel_end@ % PAGE_SIZE == 0
                    &&& entry_point@ % PAGE_SIZE == 0
                    &&& vaddr_range.start@ % PAGE_SIZE == 0
                    &&& vaddr_range.end@ % PAGE_SIZE == 0
                    &&& vaddr_range.start@ >= VADDR_UPPER_MASK
                }
)]
fn load_deko_monitor(
    ctx: DekoPPtr<DekoCpuCtx>,
    kernel_end: &mut PhysAddr,
    header: Stage2LaunchInfo,
) -> (r: Option<(VirtAddr, VaddrRange)>) {
    let elf_len = header.kernel_elf_end - header.kernel_elf_start;
    let elf_start = PhysAddr::from(header.kernel_elf_start as u64);
    let elf_end = PhysAddr::from(header.kernel_elf_end as u64);

    kinfo!("ELF range: [", elf_start => hex, " - ", elf_end => hex, "]");

    // Load the ELF file into memory.
    let elf_file = ElfFile::new(elf_start, elf_end)?;

    proof { assert(elf_file == header.get_elf().unwrap()) }

    let vaddr_alloc_base = elf_file.get_vaddr_alloc_base();
    kinfo!("Kernel load base virtual address: ", vaddr_alloc_base => hex,);

    // Map, validate and populate the  kernel ELF's PT_LOAD segments. The
    // segments' virtual address range might not necessarily be contiguous,
    // track their total extent along the way. Physical memory is successively
    // being taken from the physical memory region, the remaining space will be
    // available as heap space for the kernel. Remember the end of all
    // physical memory occupied by the loaded ELF image.
    let (vaddr_start, vaddr_end) = elf_file.load_each_segment(
        ctx,
        vaddr_alloc_base,
        kernel_end,
        header,
        Tracked(ctx_perm),
    );

    if core::intrinsics::unlikely(vaddr_start.is_none()) {
        kerror!("No loadable segment in the ELF. Likely broken");

        crate::die("");
    }
    let vaddr_start = vaddr_start.unwrap();

    // Apply relocations if any.
    // todo.

    let kernel_entry = elf_file.get_entry_point(vaddr_alloc_base);

    Some((kernel_entry, vaddr_start..vaddr_end))
}

/// Finish the boostrapping and jump into the monitor's entry point.
#[verifier::external_body]
fn into_deko_monitor(deko_entry: u64, cmd: u64) -> (__discard: !) {
    unsafe {
        core::arch::asm!(
            "jmp *%rax",
            in("rax") deko_entry,
            in("rdi") cmd,
            in("rsi") 0, /* ? */
            options(att_syntax),
        );
    }

    unreachable!();
}

} // verus!
