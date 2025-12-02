use deko_macros::DekoDebug;
use vstd::prelude::*;

use crate::prelude::*;
use crate::snp::MSR_AMD64_SEV_ES_GHCB;

verus! {

#[derive(Clone, Copy, DekoDebug)]
pub struct CpuID {
    pub eax: u32,
    pub ebx: u32,
    pub ecx: u32,
    pub edx: u32,
}

impl CpuID {
    #[verifier::external_body]
    pub fn xsave_area_size() -> (r: usize)
        ensures
            r <= PAGE_SIZE,
    {
        let cpuid = CpuID::new(0xD, 0x0);
        cpuid.ecx as usize
    }

    /// Executes the CPUID instruction with the given function and subfunction
    #[verifier::external_body]
    pub fn new(func: u64, leaf: u64) -> Self {
        let mut result_eax: u32;
        let mut result_ebx: u32;
        let mut result_ecx: u32;
        let mut result_edx: u32;
        // SAFETY: Inline assembly to execute the CPUID instruction which does
        // not change any state. Input registers (EAX, ECX) and output
        // registers (EAX, EBX, ECX, EDX) are safely managed.
        unsafe {
            core::arch::asm!("push %rbx",
                 "cpuid",
                 "movl %ebx, %edi",
                 "pop %rbx",
                 in("eax") func,
                 in("ecx") leaf,
                 lateout("eax") result_eax,
                 lateout("edi") result_ebx,
                 lateout("ecx") result_ecx,
                 lateout("edx") result_edx,
                 options(att_syntax));
        }
        Self { eax: result_eax, ebx: result_ebx, ecx: result_ecx, edx: result_edx }
    }
}

#[repr(C, packed)]
#[derive(Clone, Copy, DekoDebug)]
pub struct X86GeneralRegs {
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rbp: u64,
    pub rdi: u64,
    pub rsi: u64,
    pub rdx: u64,
    pub rcx: u64,
    pub rbx: u64,
    pub rax: u64,
}

#[verifier::external_body]
pub fn read_msr(msr: u32) -> u64 {
    let low: u32;
    let high: u32;
    unsafe {
        core::arch::asm!("rdmsr",
                in("ecx") msr,
                out("eax") low,
                out("edx") high,
            );
    }

    ((high as u64) << 32) | (low as u64)
}

#[verifier::external_body]
pub fn write_msr(msr: u32, value: u64) {
    let low: u32 = value as u32;
    let high: u32 = (value >> 32) as u32;
    unsafe {
        core::arch::asm!("wrmsr",
                in("ecx") msr,
                in("eax") low,
                in("edx") high,
            );
    }
}

/// Enter a zone where interrupts are disabled.
#[verifier::external_body]
pub fn no_irq_zone<T>(f: impl FnOnce() -> T) -> T {
    unsafe {
        core::arch::asm!("cli", options(att_syntax, preserves_flags, nomem));
    }
    let v = f();
    unsafe {
        core::arch::asm!("sti", options(att_syntax, preserves_flags, nomem));
    }

    v
}

#[verifier::external_body]
pub fn flush_tlb() {
    // Flush TLB for the new mapping
    unsafe {
        core::arch::asm!("movq %cr3, %rax", "movq %rax, %cr3", out("rax") _, options(nostack, att_syntax));
    }
}

} // verus!
verus! {

#[derive(Clone, Copy)]
pub enum GenericRegister {
    Rax,
    Rbx,
    Rcx,
    Rdx,
    Rsi,
    Rdi,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

#[derive(Clone, Copy)]
pub enum ControlRegister {
    Cr0,
    Cr2,
    Cr3,
    Cr4,
}

#[derive(Clone, Copy)]
pub enum SegmentRegister {
    Cs,
    Ds,
    Es,
    Fs,
    Gs,
    Ss,
}

/// A collection of x86_64 Registers
#[derive(Clone, Copy)]
pub enum Register {
    Generic(GenericRegister),
    Control(ControlRegister),
    Segment(SegmentRegister),
    Msr(u32),  // Model Specific Register
}

impl WellFormed for GenericRegister {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

impl WellFormed for ControlRegister {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

impl WellFormed for SegmentRegister {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

impl WellFormed for Register {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        match self {
            Self::Generic(reg) => reg.wf(),
            Self::Control(reg) => reg.wf(),
            Self::Segment(reg) => reg.wf(),
            Self::Msr(msr) => true,  // add supported MSRs.
        }
    }
}

with_permission! {
    /// Permission for a register.
    #[verifier::external_body]
    Register,
    no_copy: NoCopy,
}

/// This struct is to bypass the limitation that Verus does not support
/// [`NoCopy`] in a struct; thus if we need to mix [`NoCopy`] with other fields,
/// we need to wrap [`NoCopy`] in a separate struct.
pub ghost struct RegisterPermissionValue<V: WellFormed> {
    pub value: V,
    pub name: Register,
    pub shared: bool,
}

impl<V: WellFormed> WellFormed for RegisterPermissionValue<V> {
    open spec fn wf(&self) -> bool {
        &&& self.value.wf()
        &&& self.name.wf()
    }
}

impl RegisterPermission {
    /// Get the name of the register.
    pub uninterp spec fn name(&self) -> Register;

    /// Get the value of the register.
    pub uninterp spec fn value<V: WellFormed>(&self) -> V;

    /// Whether this permission is shared (read-only) or exclusive (read-write).
    pub uninterp spec fn shared(&self) -> bool;

    /// wellformedness invariant; needs to be generic over `V` because `value` is generic.
    pub uninterp spec fn wf(&self) -> bool;

    /// Get the view of this permission. This function is not implemented as `View`
    /// because we have to constraint genertic type `V` to be `WellFormed`.
    pub open spec fn view<V: WellFormed>(&self) -> RegisterPermissionValue<V> {
        RegisterPermissionValue { value: self.value(), name: self.name(), shared: self.shared() }
    }
}

#[verifier::external_body]
pub tracked struct DekoCpuCoreId(NoCopy);

impl DekoCpuCoreId {
    pub uninterp spec fn id(&self) -> nat;
}

/// Low-level hardware abstraction and permission tracking for CPU cores.
///
/// `DekoCpuCore` is a tracked (ghost) structure that provides the lowest-level
/// abstraction over CPU hardware and tracks all CPU-core related permissions.
/// This structure serves as the foundation for the permission-based verification
/// system and ensures that hardware resources are accessed safely.
///
/// # Architectural Relationship
///
/// `DekoCpuCore` is the highest level in the three-tier CPU context architecture:
///
/// - **`DekoCpuCore`** (this type): Low-level hardware abstraction and permission tracking
/// - **[`DekoCtx`]** (deko-core): High-level resource management and ownership
/// - **[`DekoCpuCtx`]** (deko-core): Physical per-CPU data structure and hardware interface
///
/// ## Relationship Structure
///
/// ```text
/// DekoCpuCore (This type - Permission tracking)
///     ├── cpu_core_id: Core identifier
///     ├── registers: Register permissions
///     └── privilege_level: Current ring level
///
/// DekoCtx (High-level context)
///     ├── pgtable: Page tables
///     ├── gdt: Global Descriptor Table
///     └── mapping_space: Address mappings
///
/// DekoCpuCtx (Physical CPU)
///     ├── ctx: DekoPPtr<DekoCtx>
///     ├── ghcb: GHCB (Hardware interface)
///     └── tss: TSS (Hardware state)
/// ```
///
/// # Key Responsibilities
///
/// - **Hardware Register Management**: Tracks permissions for all CPU registers
/// - **Privilege Level Control**: Manages current execution privilege (ring 0/3)
/// - **Memory Range Validation**: Defines valid kernel and heap mapping ranges
/// - **CPU Core Identification**: Provides unique identification for each core
/// - **Permission Verification**: Ensures only authorized access to hardware resources
///
/// # Permission Model
///
/// This structure implements a comprehensive permission model:
///
/// - **Exclusive Register Access**: Most registers require exclusive (read-write) permissions
/// - **Shared GHCB Access**: The GHCB MSR is read-only shared across contexts
/// - **Invariant Enforcement**: CR3 register must match the current page table
/// - **Well-Formedness**: All permissions must be properly initialized and valid
///
/// # Hardware Integration
///
/// `DekoCpuCore` provides specifications for critical hardware features:
///
/// - **Page Table Management**: Initial page table values and validation
/// - **Memory Mapping**: Kernel and heap address range definitions
/// - **Physical Memory**: Valid PTE physical address ranges
/// - **Virtual Memory**: Valid virtual address ranges for the system
///
/// # Usage in Verification
///
/// This structure is central to the formal verification system:
///
/// ```rust
/// // Typically accessed through DekoCtxPermission
/// let ctx_perm: &DekoCtxPermission = get_context_permission();
/// let cpu_core: &DekoCpuCore = &ctx_perm.current_cpu_core;
///
/// // Used for validation and specification
/// assert!(cpu_core.wf());
/// let heap_range = cpu_core.valid_heap_mapping_range();
/// let is_bsp = cpu_core.is_bsp(); // Bootstrap processor check
/// ```
///
/// # Design Principles
///
/// - **Hardware Abstraction**: Provides clean interface to x86-64 features
/// - **Permission Tracking**: Comprehensive tracking of all hardware permissions
/// - **Verification Support**: Enables formal proof of hardware access safety
/// - **Isolation**: Ensures proper CPU core isolation and resource management
///
/// # Safety Guarantees
///
/// - **Register Safety**: Prevents unauthorized register access
/// - **Memory Safety**: Validates all memory range operations
/// - **Privilege Safety**: Enforces proper privilege level management
/// - **Verification**: Enables mathematical proof of correctness
///
/// [`DekoCtx`]: deko_core::cpu::ctx::DekoCtx
/// [`DekoCpuCtx`]: deko_core::cpu::DekoCpuCtx
pub tracked struct DekoCpuCore {
    pub cpu_core_id: DekoCpuCoreId,
    pub privilege_level: nat,
    pub registers: Map<Register, RegisterPermission>,
}

impl DekoCpuCore {
    #[verifier::inline]
    pub open spec fn cpu_id(&self) -> nat {
        self.cpu_core_id.id()
    }

    #[verifier::inline]
    pub open spec fn is_bsp(&self) -> bool {
        self.cpu_id() == 0
    }

    #[verifier::inline]
    pub open spec fn is_ap(&self) -> bool {
        self.cpu_id() != 0
    }

    /// Gets the initial page table's value from the memory module.
    #[verifier::inline]
    pub open spec fn initial_page_table_value() -> u64 {
        crate::mem::initial_page_table_value()
    }

    /// Gets the valid range of PTE physical addresses from the memory module.
    #[verifier::inline]
    pub open spec fn valid_pte_phys_range() -> (u64, u64) {
        crate::mem::valid_pte_phys_range()
    }

    /// Gets the valid range of virtual addresses from the memory module.
    #[verifier::inline]
    pub open spec fn valid_pte_virt_range() -> (u64, u64) {
        crate::mem::valid_pte_virt_range()
    }

    /// Gets the valid range of kernel mapping from the memory module.
    #[verifier::inline]
    pub open spec fn valid_kernel_mapping_range(&self) -> FixedAddressMappingRange {
        crate::mem::valid_kernel_mapping_range()
    }

    /// Gets the valid range of the heap mapping area from the memory module.
    #[verifier::inline]
    pub open spec fn valid_heap_mapping_range(&self) -> FixedAddressMappingRange {
        crate::mem::valid_heap_mapping_range()
    }
}

impl WellFormed for DekoCpuCore {
    /// wellformedness invariant
    open spec fn wf(&self) -> bool {
        // Must have contained all valid registers
        &&& forall|r: Register|
            #![auto]
            {
                &&& self.registers.contains_key(r)
                &&& self.registers[r].wf()
                &&& {
                    if r != Register::Msr(MSR_AMD64_SEV_ES_GHCB) {
                        !self.registers[r].shared()  // All other registers must be exclusive

                    } else {
                        self.registers[r].shared()  // GHCB MSR must be read-only

                    }
                }
            }&&& self.registers[Register::Control(ControlRegister::Cr3)].value::<u64>()
            == crate::mem::cr3_value()  // Cr3 must be constant with the current page table

    }
}

} // verus!
