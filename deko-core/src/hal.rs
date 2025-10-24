use core::sync::atomic::{AtomicBool, Ordering};

use deko_std::prelude::*;
use vstd::prelude::*;

use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::gdt::GlobalDescriptorTable;
use crate::cpu::idt::{
    create_early_idt, stage2_generic_idt_handler, stage2_generic_idt_handler_no_ghcb, Idt,
};
use crate::cpu::register_cpuid_table;
use crate::mm::{init_frame_allocator, DEKO_MAPPING_SPACE};
use crate::snp::{get_igvm_params, Snp};

#[macro_export]
macro_rules! dispatch_to_platform {
    ($func:ident, $($args:expr),*) => {
        {
            let platform_type = match PLATFORM.get() {
                Some(pt) => pt,
                None => vstd::vpanic!("Platform not initialized"), // should not happen but could be.
            };

            match platform_type {
                PlatformType::Snp => {
                    let platform = Snp;
                    platform.$func($($args),*)
                },
                _ => vstd::vpanic!("Unsupported platform type"),
            }
        }
    };
}

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

/// This defines a platform abstraction to permit the Deko to run on different
/// backend CVMs. This also gives verus to reason about the high-level verifi-
/// cation logics without resorting to low-level details of the platform.
pub trait PlatformApi: Sync + Send + WellFormed {
    /// Returns the platform type of the current platform.
    fn platform_type(&self) -> PlatformType;

    /// Initializes the platform. This function should be called once at the
    /// beginning of the program to set up the platform-specific environment.
    fn init_platform(&self, header: Stage2LaunchInfo)
        requires
            header.wf(),
            self.wf(),
    ;

    fn validate_memory(
        &self,
        Tracked(ctx): Tracked<&mut DekoCtxPermission>,
        heap_start: u64,
        heap_end: u64,
    ) -> (r: bool)
        requires
            self.wf(),
            old(ctx).wf(),
            heap_end > heap_start,
            heap_start % 0x1000 == 0,
            heap_end % 0x1000 == 0,
            heap_end <= LOWMEM_END as u64,
        ensures
            ctx.wf(),
    {
        true
    }
}

/// Injects dummy handlers into the IDT so that we can do early-stage
/// exception handling (although this does nothing for now).
#[inline(always)]
fn init_early_idt(idt: &mut Idt)
    requires
        old(idt).entries.wf(),
    ensures
        idt.wf(),
{
    crate::cpu::idt::init_early_idt(idt);
}

#[inline(always)]
fn init_early_idt_late(idt: &mut Idt)
    requires
        old(idt).wf(),
    ensures
        idt.wf(),
{
    crate::cpu::idt::init_generic_idt(idt);
}

/// Sets up the environment for the platform which will setup the GDT, kernel mapping, paging,
/// kernel loading, heaps, etc.
#[verifier::exec_allows_no_decreases_clause]
pub fn setup_env(ctx: DekoPPtr<DekoCtx>, ctx_perm: Tracked<DekoCtxPermission>) -> (__discard: !)
    requires
        ctx_perm@.wf_with(ctx),
        ctx_perm@.current_cpu_core.is_bsp(),
{
    let Tracked(mut ctx_perm) = ctx_perm;

    // Extract the launch info from the context.
    let header = ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).stage2_launch_info.borrow(
        Tracked(&ctx_perm.stage2_launch_info_perm),
    ).clone();

    // Set up the GDT.
    GlobalDescriptorTable::init_gdt(Tracked(&ctx_perm.current_cpu_core));

    let platform_type = PlatformType::from(header.platform_type);
    PLATFORM.init(platform_type.clone());

    let snp = Snp;

    // Initialize the IDT.
    let mut idt = Idt { entries: create_early_idt() };
    init_early_idt(&mut idt);

    // Do some platform-specific stuff.
    dispatch_to_platform!(init_platform, header);

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

    snp.validate_memory(Tracked(&mut ctx_perm), 0, LOWMEM_END as u64);

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
    dispatch_to_platform!(init_each_cpu, ctx, ctx_perm);

    
    init_early_idt_late(&mut idt);
    
    dispatch_to_platform!(init_platform_end, get_igvm_params(&header));
    
    // will not crash; good news.
    loop {
    }
}

} // verus!
