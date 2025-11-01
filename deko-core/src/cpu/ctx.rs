use deko_std::prelude::*;
use vstd::prelude::*;

use crate::cpu::gdt::GlobalDescriptorTable;
use crate::mm::paging::{
    bit_not_in_addr_region, bit_not_overlapping, PageTable, PageTablePermission,
};

verus! {

/// High-level execution context providing exclusive access to a CPU core's resources.
///
/// `DekoCtx` encapsulates all resources, ghost state, and runtime state that belong
/// exclusively to the executing CPU core. By centralizing ownership in this context,
/// we prevent unauthorized resource access and maintain the invariants required for
/// permission-based verification.
///
/// # Architectural Relationship
///
/// `DekoCtx` is part of a three-tier CPU context architecture:
///
/// - **[`DekoCpuCore`]** (deko-std): Low-level hardware abstraction and permission tracking
/// - **`DekoCtx`** (this type): High-level resource management and ownership
/// - **[`DekoCpuCtx`]** (deko-core): Physical per-CPU data structure and hardware interface
///
/// ## Relationship Structure
///
/// ```text
/// DekoCpuCtx (Physical CPU)
///     ├── ctx: DekoPPtr<DekoCtx> ← This type
///     ├── ghcb: GHCB (Hardware interface)
///     └── tss: TSS (Hardware state)
///
/// DekoCtx (This type - Execution context)
///     ├── pgtable: Page tables
///     ├── gdt: Global Descriptor Table
///     └── mapping_space: Address mappings
///
/// DekoCpuCore (Permission tracking)
///     ├── cpu_core_id: Core identifier
///     ├── registers: Register permissions
///     └── privilege_level: Current ring level
/// ```
///
/// # Design Principles
///
/// - **Resource Ownership**: Centralizes ownership of all CPU core resources
/// - **Exclusive Access**: Cannot be cloned or copied to prevent sharing violations
/// - **Permission-Based**: All access requires explicit permission structures
/// - **Verification-Ready**: Enables formal verification of memory safety
///
/// # Requirements
///
/// - Must be passed as a parameter to all functions accessing core-local resources
/// - Cannot be cloned, stored globally, or shared between cores
/// - Assembled exactly once at each core's entry function
/// - Always accessed through [`DekoCpuCtx`] which holds a pointer to this context
///
/// # Usage Pattern
///
/// ```rust
/// // 1. Get the physical CPU context
/// let (cpu_ctx, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
///
/// // 2. Access this high-level execution context
/// let deko_ctx = cpu_ctx.borrow(Tracked(&cpu_perm.ptr_perm)).ctx;
///
/// // 3. Use with proper permissions
/// some_operation(deko_ctx, Tracked(&cpu_perm.ctx_perm));
/// ```
///
/// [`DekoCpuCore`]: deko_std::cpu::DekoCpuCore
/// [`DekoCpuCtx`]: crate::cpu::DekoCpuCtx
#[repr(C)]
pub struct DekoCtx {
    pub stage2_launch_info: DekoPPtr<Stage2LaunchInfo>,
    pub pgtable: DekoPPtr<PageTable>,
    pub gdt: DekoPPtr<GlobalDescriptorTable>,
    pub mapping_space: MappingSpace,
}

impl DekoCtx {
    pub uninterp spec fn cpu_id(&self) -> nat;
}

/// Permission structure for accessing and modifying [`DekoCtx`] resources.
///
/// `DekoCtxPermission` is a tracked (ghost) structure that encapsulates all the
/// permissions required to safely access and modify the resources owned by a
/// [`DekoCtx`]. This is a key component of the permission-based verification
/// system that ensures memory safety and prevents unauthorized access.
///
/// # Architectural Role
///
/// This permission structure bridges the three-tier CPU context architecture:
///
/// - Contains a [`DekoCpuCore`] for hardware-level permission tracking
/// - Provides access permissions for [`DekoCtx`] and all its owned resources
/// - Ensures consistency between hardware state and high-level context
///
/// # Permission Components
///
/// - **`current_cpu_core`**: Hardware abstraction and register permissions
/// - **`deko_ctx_ptr_perm`**: Permission to access the [`DekoCtx`] structure itself
/// - **`stage2_launch_info_perm`**: Access to boot/launch information
/// - **`pgtable_perm`**: Page table modification permissions
/// - **`gdt_perm`**: Global Descriptor Table access permissions
/// - **`mapping_space`**: Virtual-to-physical address mapping definitions
///
/// # Verification Invariants
///
/// The permission structure maintains several critical invariants:
///
/// - CPU core ID consistency across all components
/// - Memory range validity for heap and kernel mappings
/// - Page table entries within valid physical ranges
/// - Proper initialization of all permission components
///
/// # Usage Pattern
///
/// ```rust
/// // Permissions are typically obtained through DekoCpuCtx
/// let (cpu_ctx, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
///
/// // The ctx_perm field contains this permission structure
/// let ctx_perm: &DekoCtxPermission = &cpu_perm.ctx_perm;
///
/// // Use permissions to access resources safely
/// let deko_ctx = cpu_ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).ctx;
/// modify_page_table(deko_ctx, Tracked(&ctx_perm.pgtable_perm));
/// ```
///
/// # Safety Guarantees
///
/// - **Exclusive Access**: Only one permission structure per CPU core
/// - **Resource Consistency**: All permissions refer to the same CPU's resources
/// - **Memory Safety**: Prevents access to invalid or uninitialized memory
/// - **Verification**: Enables formal proof of correctness properties
///
/// [`DekoCpuCore`]: deko_std::cpu::DekoCpuCore
pub tracked struct DekoCtxPermission {
    pub current_cpu_core: DekoCpuCore,
    pub deko_ctx_ptr_perm: DekoPointsTo<DekoCtx>,
    pub stage2_launch_info_perm: DekoPointsTo<Stage2LaunchInfo>,
    pub pgtable_perm: PageTablePermission,
    pub gdt_perm: DekoPointsTo<GlobalDescriptorTable>,
    pub mapping_space: MappingSpace,
}

// `NoCopy` is external; we do not want to create a seperate tracked struct again.
#[verifier::external]
impl !Copy for DekoCtx {

}

#[verifier::external]
impl !Clone for DekoCtx {

}

impl WellFormed for DekoCtx {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl WellFormed for DekoCtxPermission {
    open spec fn wf(&self) -> bool {
        let heap_mapping = self.current_cpu_core.valid_heap_mapping_range();
        let heap_phys_start = heap_mapping.phys_start@;
        let heap_phys_end = heap_mapping.virt_end@ - heap_mapping.virt_start@
            + heap_mapping.phys_start@;

        &&& self.current_cpu_core.cpu_id() == self.deko_ctx_ptr_perm.value().cpu_id()
        &&& self.current_cpu_core.wf()
        &&& self.stage2_launch_info_perm.is_init() && self.stage2_launch_info_perm.wf()
        &&& self.pgtable_perm.wf()
        &&& self.gdt_perm.wf()  // gdt can be uninitialized at first
        &&& {
            &&& self.deko_ctx_ptr_perm.is_init() && self.deko_ctx_ptr_perm.wf()
            &&& self.deko_ctx_ptr_perm.value().stage2_launch_info@
                === self.stage2_launch_info_perm.pptr()
            &&& self.deko_ctx_ptr_perm.value().pgtable@ === self.pgtable_perm.pgtable_perm.pptr()
            &&& self.deko_ctx_ptr_perm.value().gdt@ === self.gdt_perm.pptr()
        }
        &&& self.mem_range_wf()
        &&& self.pgtable_perm.pte_within_range(heap_phys_start as u64, heap_phys_end as u64)
        &&& self.pgtable_perm.region_mapped(heap_mapping)
        &&& self.pgtable_perm.identity_mapped(heap_mapping)
    }
}

impl DekoCtxPermission {
    pub open spec fn wf_with(&self, ctx: DekoPPtr<DekoCtx>) -> bool {
        &&& self.wf()
        &&& ctx@ === self.deko_ctx_ptr_perm.pptr()
        &&& bit_not_overlapping(self.shared_bit())
        &&& bit_not_overlapping(self.private_bit())
        &&& bit_not_in_addr_region(self.shared_bit())
        &&& bit_not_in_addr_region(self.private_bit())
    }

    /// Get the shared bit mask for this context.
    pub uninterp spec fn shared_bit(&self) -> u64;

    /// Get the private bit mask for this context.
    pub uninterp spec fn private_bit(&self) -> u64;

    /// Valid memory regions.
    pub open spec fn mem_range_wf(&self) -> bool {
        let ms = self.mapping_space;

        &&& ms.wf()
        &&& ms.kernel == self.current_cpu_core.valid_kernel_mapping_range()
        &&& ms.physmap == self.current_cpu_core.valid_heap_mapping_range()
    }

    pub open spec fn in_heap_range(&self, paddr: PhysAddr) -> bool {
        let heap_mapping = self.current_cpu_core.valid_heap_mapping_range();
        let start = heap_mapping.phys_start@;
        let end = heap_mapping.virt_end@ - heap_mapping.virt_start@ + heap_mapping.phys_start@;

        &&& paddr.wf()
        &&& start <= paddr@ < end
    }
}

} // verus!
