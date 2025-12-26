use deko_macros::deko_const_decl;
use vstd::prelude::*;

use crate::prelude::*;

verus! {

global layout usize is size == 8;

global layout u64 is size == 8;

// Note on the constants: Verus is having trouble verifying
// non-overflow/underflow of some arithmetic operations that
// involve constants and bit operations.
//
// We resort to hardcoding some of the results.
// FIXME: Make virtual address canonical (must be sign extended)
/// Size helpers
pub const SIZE_1K: u64 = 1024;

pub const SIZE_1M: u64 = SIZE_1K * 1024;

pub const SIZE_1G: u64 = SIZE_1M * 1024;

/// Pagesize definitions
pub const PAGE_SIZE: u64 = SIZE_1K * 4;

pub const PAGE_SIZE_2M: u64 = SIZE_1M * 2;

/// More size helpers
// pub const SIZE_LEVEL3: u64 = 1u64 << ((9 * 3) + 12);
// pub const SIZE_LEVEL2: u64 = 1u64 << ((9 * 2) + 12);
// pub const SIZE_LEVEL1: u64 = 1u64 << ((9 * 1) + 12);
// pub const SIZE_LEVEL0: u64 = 1u64 << ((9 * 0) + 12);
pub const SIZE_LEVEL3: u64 = 0x8000000000;

pub const SIZE_LEVEL2: u64 = 0x40000000;

pub const SIZE_LEVEL1: u64 = 0x200000;

pub const SIZE_LEVEL0: u64 = 0x1000;

// Stack definitions
pub const STACK_PAGES: u64 = 13;

pub const STACK_SIZE: u64 = PAGE_SIZE * STACK_PAGES;

pub const STACK_GUARD_SIZE: u64 = STACK_SIZE;

pub const STACK_TOTAL_SIZE: u64 = STACK_SIZE + STACK_GUARD_SIZE;

/// Level3 page-table index shared between all CPUs
pub const PGTABLE_LVL3_IDX_SHARED: u64 = 511;

/// Base Address of shared memory region
// pub const GLOBAL_BASE: VirtAddr = VirtAddr(PGTABLE_LVL3_IDX_SHARED << ((3 * 9) + 12));
// FIXME: Hardcoded due to verus verification issues
pub const GLOBAL_BASE: VirtAddr = VirtAddr(0xFF8000000000);

pub const GLOBAL_MAPPING_SIZE: u64 = 256 * SIZE_1G;

/// Shared mappings region start
// pub const GLOBAL_MAPPING_BASE: VirtAddr = VirtAddr(GLOBAL_BASE.0 + GLOBAL_MAPPING_SIZE);
/// Shared mappings region end
// pub const GLOBAL_MAPPING_END: VirtAddr = VirtAddr(GLOBAL_MAPPING_BASE.0 + (SIZE_1G));
/// Mapping address for Hyper-V hypercall page.
// pub const HYPERCALL_CODE_PAGE: VirtAddr = VirtAddr(GLOBAL_MAPPING_BASE.0 - PAGE_SIZE);
/// PerCPU mappings level 3 index
pub const PGTABLE_LVL3_IDX_PERCPU: u64 = 510;

/// Base Address of shared memory region
// pub const PERCPU_BASE: VirtAddr = VirtAddr(PGTABLE_LVL3_IDX_PERCPU << ((3 * 9) + 12));
// FIXME: Hardcoded due to verus verification issues
pub const PERCPU_BASE: VirtAddr = VirtAddr(0xFFFF_FF00_0000_0000);

/// End Address of per-cpu memory region
pub const PERCPU_END: VirtAddr = VirtAddr(0xFFFF_FF80_0000_0000);

deko_const_decl!(
    /// PerCPU CAA mappings
    PERCPU_CAA_BASE,
    VirtAddr,
    VirtAddr((PERCPU_BASE.0 + (2 * SIZE_LEVEL0)) as u64),
    VirtAddr(PERCPU_BASE.0 + (2 * SIZE_LEVEL0)),
);

deko_const_decl!(
    /// PerCPU VMSA mappings
    PERCPU_VMSA_BASE,
    VirtAddr,
    VirtAddr((PERCPU_BASE.0 + (4 * SIZE_LEVEL0)) as u64),
    VirtAddr(PERCPU_BASE.0 + (4 * SIZE_LEVEL0)),
);

deko_const_decl!(
    /// Region for PerCPU Stacks
    PERCPU_STACKS_BASE,
    VirtAddr,
    VirtAddr((PERCPU_BASE.0 + SIZE_LEVEL1) as u64),
    VirtAddr(PERCPU_BASE.0 + SIZE_LEVEL1),
);

deko_const_decl!(
    /// Shadow stack address of the per-cpu init task
    SHADOW_STACKS_INIT_TASK,
    VirtAddr,
    PERCPU_STACKS_BASE,
    PERCPU_STACKS_BASE,
);

deko_const_decl!(
    /// Stack address to use during context switches
    CONTEXT_SWITCH_STACK,
    VirtAddr,
    VirtAddr((SHADOW_STACKS_INIT_TASK.0 + (STACK_TOTAL_SIZE)) as u64),
    VirtAddr(SHADOW_STACKS_INIT_TASK.0 + (STACK_TOTAL_SIZE)),
);

deko_const_decl!(
    /// Shadow stack address to use during context switches
    CONTEXT_SWITCH_SHADOW_STACK,
    VirtAddr,
    VirtAddr((CONTEXT_SWITCH_STACK.0 + (STACK_TOTAL_SIZE)) as u64),
    VirtAddr(CONTEXT_SWITCH_STACK.0 + (STACK_TOTAL_SIZE)),
);

deko_const_decl!(
    /// IST Stacks base address
    STACKS_IST_BASE,
    VirtAddr,
    VirtAddr((CONTEXT_SWITCH_SHADOW_STACK.0 + (STACK_TOTAL_SIZE)) as u64),
    VirtAddr(CONTEXT_SWITCH_SHADOW_STACK.0 + (STACK_TOTAL_SIZE)),
);

deko_const_decl!(
    /// DoubleFault IST stack base address
    STACK_IST_DF_BASE,
    VirtAddr,
    STACKS_IST_BASE,
    STACKS_IST_BASE,
);

deko_const_decl!(
    /// DoubleFault ISST shadow stack base address
    SHADOW_STACK_ISST_DF_BASE,
    VirtAddr,
    VirtAddr((STACKS_IST_BASE.0 + (STACK_TOTAL_SIZE)) as u64),
    VirtAddr(STACKS_IST_BASE.0 + (STACK_TOTAL_SIZE)),
);

deko_const_decl!(
    /// PerCPU XSave Context area base address
    XSAVE_AREA_BASE,
    VirtAddr,
    VirtAddr((SHADOW_STACK_ISST_DF_BASE.0 + (STACK_TOTAL_SIZE)) as u64),
    VirtAddr(SHADOW_STACK_ISST_DF_BASE.0 + (STACK_TOTAL_SIZE)),
);

deko_const_decl!(
    /// Base Address for temporary mappings - used by page-table guards
    PERCPU_TEMP_BASE,
    VirtAddr,
    VirtAddr((PERCPU_BASE.0 + (SIZE_LEVEL2)) as u64),
    VirtAddr(PERCPU_BASE.0 + (SIZE_LEVEL2)),
);

// Below is space for 512 temporary 4k mappings and 511 temporary 2M mappings
deko_const_decl!(
    /// Start and End for PAGE_SIZEed temporary mappings
    PERCPU_TEMP_BASE_4K,
    VirtAddr,
    PERCPU_TEMP_BASE,
    PERCPU_TEMP_BASE,
);

deko_const_decl!(
    /// Start and End for PAGE_SIZEed temporary mappings
    PERCPU_TEMP_END_4K,
    VirtAddr,
    VirtAddr((PERCPU_TEMP_BASE_4K.0 + (SIZE_LEVEL1)) as u64),
    VirtAddr(PERCPU_TEMP_BASE_4K.0 + (SIZE_LEVEL1)),
);

deko_const_decl!(
    /// Start and End for PAGE_SIZEed temporary mappings
    PERCPU_TEMP_BASE_2M,
    VirtAddr,
    VirtAddr((PERCPU_TEMP_BASE.0 + (SIZE_LEVEL1)) as u64),
    VirtAddr(PERCPU_TEMP_BASE.0 + (SIZE_LEVEL1)),
);

deko_const_decl!(
    /// Start and End for PAGE_SIZEed temporary mappings
    PERCPU_TEMP_END_2M,
    VirtAddr,
    VirtAddr((PERCPU_TEMP_BASE.0 + (SIZE_LEVEL2)) as u64),
    VirtAddr(PERCPU_TEMP_BASE.0 + (SIZE_LEVEL2)),
);

/// Task mappings level 3 index
pub const PGTABLE_LVL3_IDX_PERTASK: u64 = 508;

/// Base address of task memory region
// pub const PERTASK_BASE: VirtAddr = VirtAddr(PGTABLE_LVL3_IDX_PERTASK << ((3 * 9) + 12));
// FIXME: Hardcoded due to verus verification issues
pub const PERTASK_BASE: VirtAddr = VirtAddr(0xFE0000000000);

deko_const_decl!(
    /// End address of task memory region
    PERTASK_END,
    VirtAddr,
    VirtAddr((PERTASK_BASE.0 + (SIZE_LEVEL3)) as u64),
    VirtAddr(PERTASK_BASE.0 + (SIZE_LEVEL3)),
);

/// Page table self-map level 3 index
pub const PGTABLE_LVL3_IDX_PTE_SELFMAP: u64 = 493;

// pub const PTE_BASE: VirtAddr = VirtAddr(PGTABLE_LVL3_IDX_PTE_SELFMAP << ((3 * 9) + 12));
// FIXME: Hardcoded due to verus verification issues
pub const PTE_BASE: VirtAddr = VirtAddr(0xFFFFF68000000000);

//
// User-space mapping constants
//
/// Start of user memory address range
pub const USER_MEM_START: VirtAddr = VirtAddr(0);

deko_const_decl!(
    /// End of user memory address range
    USER_MEM_END,
    VirtAddr,
    VirtAddr((USER_MEM_START.0 + (256 * SIZE_LEVEL3)) as u64),
    VirtAddr(USER_MEM_START.0 + (256 * SIZE_LEVEL3)),
);

pub const PAGE_TABLE_ENTRY: usize = 0x200;

} // verus!
