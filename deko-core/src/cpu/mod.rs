pub mod ctx;
pub mod gdt;
pub mod idt;
pub mod irq;
pub mod msr;
pub mod regs;
pub mod types;

use deko_macros::DekoDebug;
use deko_std::prelude::*;
use deko_std::snp::ghcb::GuestHostCommucationBlock;
use vstd::atomic::{PAtomicBool, PAtomicU32, PermissionBool, PermissionU32};
use vstd::cell::{PCell, PointsTo};
use vstd::prelude::*;

use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::mm::paging::{
    bit_not_in_addr_region, bit_not_overlapping, Mapping, Page, PageTable, PageTablePermission,
    PteFlags,
};
use crate::mm::stack::DekoKernelStack;
use crate::mm::virt_to_phys;
use crate::mm::vm::{VirtualMemoryRegion, VirtualMemoryRegionPermission};

verus! {

pub const CPUID_MAX_COUNT: usize = 128;

pub const CPU_AREA_MAGIC: u64 = 0x114514;

pub struct GuestVmsaRef {
    vmsa: Option<PhysAddr>,
    caa: Option<PhysAddr>,
    generation: u64,
    gen_in_use: u64,
}

impl WellFormed for GuestVmsaRef {
    closed spec fn wf(&self) -> bool {
        &&& self.vmsa matches Some(p) ==> p.wf()
        &&& self.caa matches Some(p) ==> p.wf()
    }
}

#[repr(C, packed(4))]
#[derive(DekoDebug)]
pub struct X86Tss {
    reserved0: u32,
    stacks: Array<u64, 3>,
    _reserved1: u64,
    ist_stacks: Array<u64, 7>,
    _reserved2: u64,
    _reserved3: u16,
    io_bmp_base: u16,
}

#[derive(DekoDebug)]
pub struct PerCpuShared {
    apic_id: u32,  // the id of the local apic
    cpu_index: usize,
    #[deko(skip)]
    guest_vmsa: RwLockNoPred<GuestVmsaRef>,
    #[deko(skip)]
    online: (PAtomicBool, Tracked<PermissionBool>),
    #[deko(skip)]
    ipi_irr: Array<(PAtomicU32, Tracked<PermissionU32>), 8>,
    #[deko(skip)]
    ipi_pending: (PAtomicBool, Tracked<PermissionBool>),
    #[deko(skip)]
    nmi_pending: (
        PAtomicBool,
        Tracked<PermissionBool>,
    ),
    // ipi_state: IpiState, todo
}

impl WellFormed for PerCpuShared {
    closed spec fn wf(&self) -> bool {
        &&& self.apic_id == self.cpu_index
        &&& self.cpu_index < CPUID_MAX_COUNT
        &&& self.guest_vmsa.wf()
        &&& self.online.1@.id() == self.online.0.id()
        &&& self.ipi_pending.1@.id() == self.ipi_pending.0.id()
        &&& self.nmi_pending.1@.id() == self.nmi_pending.0.id()
        &&& self.ipi_irr.wf()
        &&& forall|i: int|
            0 <= i && i < 8 ==> #[trigger] self.ipi_irr@[i as int].1@.id()
                == self.ipi_irr@[i as int].0.id() && self.ipi_irr@[i as int].wf()
    }
}

impl PerCpuShared {
    #[verifier::external_body]
    #[inline(always)]
    const fn new_ipi_irr() -> (r: Array<(PAtomicU32, Tracked<PermissionU32>), 8>)
        ensures
            r.wf(),
            forall|i: int|
                #![trigger r@[i as int]]
                0 <= i && i < 8 ==> {
                    &&& r@[i as int].wf()
                    &&& r@[i as int].1@.id() == r@[i as int].0.id()
                },
    {
        Array::new([const { (PAtomicU32::new(0)) };8])
    }

    pub const fn new() -> (r: Self)
        ensures
            r.wf(),
    {
        let online = PAtomicBool::new(false);
        let ipi_pending = PAtomicBool::new(false);
        let nmi_pending = PAtomicBool::new(false);
        let ipi_irr = Self::new_ipi_irr();
        let guest_vmsa = RwLockNoPred::new(
            GuestVmsaRef { vmsa: None, caa: None, generation: 0, gen_in_use: 0 },
            Ghost(TrivialPredicate::new()),
        );

        proof {
            use_type_invariant(&guest_vmsa);
        }

        PerCpuShared {
            apic_id: 0,
            cpu_index: 0,
            guest_vmsa,
            online,
            ipi_irr,
            ipi_pending,
            nmi_pending,
        }
    }
}

#[derive(DekoDebug)]
pub struct PerCpuAreas(pub Array<PerCpuShared, CPUID_MAX_COUNT>);

impl WellFormed for PerCpuAreas {
    open spec fn wf(&self) -> bool {
        &&& self.0.wf()
        &&& forall|i: int|
            0 <= i && i < CPUID_MAX_COUNT as int ==> #[trigger] self.0@[i as int].wf()
    }
}

pub struct PerCpuAreasInv;

impl RwLockPredicate<PerCpuAreas> for PerCpuAreasInv {
    open spec fn inv(self, v: PerCpuAreas) -> bool {
        v.wf()
    }
}

impl PerCpuAreas {
    #[verifier::external_body]
    pub const fn new() -> (r: Self)
        ensures
            r.wf(),
    {
        // This feature is not yet supported by verus.
        PerCpuAreas(Array::new([const { PerCpuShared::new() };CPUID_MAX_COUNT]))
    }
}

impl View for PerCpuAreas {
    type V = Seq<PerCpuShared>;

    closed spec fn view(&self) -> Self::V {
        self.0@
    }
}

/// This is a global list of per-cpu areas. Although we can implement this in
/// a lock-free but this would otherwise create a lot of complexity.
///
/// For verification and the ease of implementation, we just use a simple
/// read-write lock to protect the access to this structure.
pub exec static PERCPU_AREAS: RwLock<PerCpuAreas, PerCpuAreasInv>
    ensures
        PERCPU_AREAS.wf(),
{
    let lock = RwLock::new(PerCpuAreas::new(), Ghost(PerCpuAreasInv {  }));
    proof {
        use_type_invariant(&lock);
    }

    lock
}

/// Physical per-CPU data structure and hardware interface.
///
/// `DekoCpuCtx` represents the physical per-CPU area that contains all CPU-specific
/// state and provides the hardware interface for the Deko hypervisor. This structure
/// is mapped at a fixed virtual address (`PERCPU_BASE`) for each CPU core and serves
/// as the entry point for accessing CPU-local resources.
///
/// # Architectural Relationship
///
/// `DekoCpuCtx` is the lowest level in the three-tier CPU context architecture:
///
/// - **[`DekoCpuCore`]** (deko-std): Low-level hardware abstraction and permission tracking
/// - **[`DekoCtx`]** (deko-core): High-level resource management and ownership
/// - **[`DekoCpuCtx`]** (this type): Physical per-CPU data structure and hardware interface
///
/// ## Relationship Structure
///
/// ```text
/// DekoCpuCtx (This type - Physical CPU)
///     ├── ctx: DekoPPtr<DekoCtx> → High-level context
///     ├── ghcb: GHCB (Hardware interface)
///     ├── tss: TSS (Hardware state)
///     └── shared_area: Per-CPU shared data
///
/// DekoCtx (High-level context)
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
/// # Key Components
///
/// - **`ctx`**: Pointer to the high-level [`DekoCtx`] execution context
/// - **`ghcb`**: Guest-Host Communication Block for AMD SEV-SNP
/// - **`tss`**: Task State Segment for x86-64 hardware
/// - **`shared_area`**: Pointer to shared per-CPU data structures
/// - **`private_bit/shared_bit`**: Memory confidentiality control bits
///
/// # Hardware Interface
///
/// This structure provides the primary interface to hardware features:
///
/// - **Memory Confidentiality**: Controls private/shared memory bits
/// - **Guest-Host Communication**: GHCB for hypervisor calls
/// - **Task Switching**: TSS for hardware task management
/// - **Per-CPU Storage**: Fixed virtual address mapping
///
/// # Usage Pattern
///
/// ```rust
/// // 1. Get the current CPU's context (always succeeds)
/// let (cpu_ctx, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
///
/// // 2. Access the high-level execution context
/// let deko_ctx = cpu_ctx.borrow(Tracked(&cpu_perm.ptr_perm)).ctx;
///
/// // 3. Use hardware features
/// cpu_ctx.map_shared_page(vaddr, Tracked(cpu_perm));
/// ```
///
/// # Memory Layout
///
/// Each `DekoCpuCtx` is mapped at `PERCPU_BASE + (cpu_id * PAGE_SIZE)` and contains:
///
/// - Magic number for validation
/// - CPU identification and state
/// - Hardware interface structures
/// - Pointers to other context levels
///
/// # Safety Guarantees
///
/// - **Fixed Mapping**: Always accessible at known virtual address
/// - **Per-CPU Isolation**: Each CPU has its own independent instance
/// - **Hardware Integration**: Direct interface to x86-64 and SEV-SNP features
/// - **Permission Control**: All access requires proper permission structures
///
/// [`DekoCpuCore`]: deko_std::cpu::DekoCpuCore
/// [`DekoCtx`]: crate::cpu::ctx::DekoCtx
#[derive(DekoDebug)]
pub struct DekoCpuCtx {
    pub magic: u64,
    #[deko(hex)]
    pub cpu_id: u64,
    /// The GHCB block for this CPU.
    ghcb: DekoPPtr<GuestHostCommucationBlock>,
    tss: X86Tss,
    /// The page table for this CPU.
    shared_area: DekoPPtr<PerCpuShared>,
    /// The page table of this CPU.
    pgtable: DekoPPtr<PageTable>,
    /// The stack for doing context switches.
    ctx_switch_stack: Option<DekoPPtr<DekoKernelStack>>,
    /// The private bit of the PTE of this core.
    #[deko(hex)]
    private_bit: u64,
    /// The shared bit of the PTE of this core.
    #[deko(hex)]
    shared_bit: u64,
    /// The high-level kernel mapping context for this CPU.
    kernel_mapping: MappingSpace,
    /// The virtual memory region used for per-cpu area.
    /// At stage2 this is [`Option::None`].
    vm_region: Option<VirtualMemoryRegion>,
}

with_permission! {
    DekoCpuCtx,
    ptr_perm: DekoPointsTo<DekoCpuCtx>,
    pgtable_perm: PageTablePermission,
    ghcb_perm: DekoPointsTo<GuestHostCommucationBlock>,
    vm_region_perm: Option<VirtualMemoryRegionPermission>,
}

impl DekoCpuCtxPermission {
    #[verifier::inline]
    pub open spec fn has_self_mapped(&self) -> bool
        recommends
            self.wf(),
    {
        self.pgtable_perm.virt_to_frame_spec(PERCPU_BASE) matches Some(_)
    }

    pub open spec fn wf_with(&self, cpu_data: DekoPPtr<DekoCpuCtx>) -> bool {
        &&& self.ptr_perm.pptr() == cpu_data@
        &&& self.ptr_perm.value().vm_region() matches Some(vm) ==> self.vm_region_perm matches Some(
            perm,
        ) && {
            &&& perm.pgtable_perm.wf()
            &&& perm.vm_perms.wf()
            &&& vm.wf_with(&perm)
        }
        &&& self.wf()
    }
}

impl WellFormed for DekoCpuCtxPermission {
    open spec fn wf(&self) -> bool {
        &&& self.ptr_perm.is_init()
        &&& self.ptr_perm.wf()
        &&& self.ptr_perm.value().kernel_mapping().wf()
        // &&& self.ptr_perm.value().ctx_switch_stack().wf()
        &&& self.pgtable_perm.wf()
        &&& self.pgtable_perm.pgtable_perm.pptr() == self.ptr_perm.value().pgtable_spec()@
        &&& self.pgtable_perm.mapping_space === self.ptr_perm.value().kernel_mapping_spec()
        &&& self.pgtable_perm.private_bit == self.ptr_perm.value().private_bit_spec()
        &&& self.pgtable_perm.shared_bit == self.ptr_perm.value().shared_bit_spec()
        &&& bit_not_in_addr_region(self.pgtable_perm.private_bit)
        &&& bit_not_in_addr_region(self.pgtable_perm.shared_bit)
        &&& bit_not_overlapping(self.pgtable_perm.private_bit)
        &&& bit_not_overlapping(self.pgtable_perm.shared_bit)
        &&& self.ghcb_perm.is_init()
        &&& self.ghcb_perm.wf()
        &&& self.ghcb_perm.pptr() == self.ptr_perm.value().ghcb_spec()@
    }
}

#[repr(C, packed)]
#[derive(Clone, Copy)]
pub struct CpuidFn {
    pub eax_in: u32,
    pub ecx_in: u32,
    pub xcr0_in: u64,
    pub xss_in: u64,
    pub eax_out: u32,
    pub ebx_out: u32,
    pub ecx_out: u32,
    pub edx_out: u32,
    pub reserved_1: u64,
}

impl CpuidFn {
    pub open spec fn empty() -> Self {
        CpuidFn {
            eax_in: 0,
            ecx_in: 0,
            xcr0_in: 0,
            xss_in: 0,
            eax_out: 0,
            ebx_out: 0,
            ecx_out: 0,
            edx_out: 0,
            reserved_1: 0,
        }
    }
}

impl Default for CpuidFn {
    fn default() -> (r: Self)
        ensures
            r == Self::empty(),
    {
        CpuidFn {
            eax_in: 0,
            ecx_in: 0,
            xcr0_in: 0,
            xss_in: 0,
            eax_out: 0,
            ebx_out: 0,
            ecx_out: 0,
            edx_out: 0,
            reserved_1: 0,
        }
    }
}

#[repr(C, packed)]
pub struct CpuidTable {
    pub count: u32,
    pub reserved_1: u32,
    pub reserved_2: u64,
    pub func: Array<CpuidFn, CPUID_MAX_COUNT>,
}

impl View for CpuidTable {
    type V = Seq<CpuidFn>;

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        self.func@
    }
}

impl Default for CpuidTable {
    fn default() -> (r: Self)
        ensures
            r.wf(),
            r.count == 0,
            r.reserved_1 == 0,
            r.reserved_2 == 0,
            r@ =~= Seq::new(CPUID_MAX_COUNT as nat, |i| CpuidFn::empty()),
    {
        broadcast use deko_std::array::lemma_sized_t_makes_sized_array;

        CpuidTable { count: 0, reserved_1: 0, reserved_2: 0, func: Array::fill(CpuidFn::default()) }
    }
}

impl CpuidTable {
    pub fn new() -> (r: Self)
        ensures
            r.wf(),
            r.count == 0,
            r.reserved_1 == 0,
            r.reserved_2 == 0,
            r@ =~= Seq::new(CPUID_MAX_COUNT as nat, |i| CpuidFn::empty()),
    {
        CpuidTable::default()
    }
}

impl WellFormed for CpuidFn {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

impl WellFormed for CpuidTable {
    open spec fn wf(&self) -> bool {
        &&& self.func.wf()
    }
}

impl WellFormed for X86Tss {
    closed spec fn wf(&self) -> bool {
        &&& self.stacks.wf()
        &&& self.ist_stacks.wf()
    }
}

impl WellFormed for DekoCpuCtx {
    closed spec fn wf(&self) -> bool {
        &&& self.tss.wf()
        &&& self.cpu_id < CPUID_MAX_COUNT as u64
        &&& self.magic == CPU_AREA_MAGIC
    }
}

impl X86Tss {

}

impl DekoCpuCtx {
    uninterp spec fn addr(&self) -> u64;

    pub closed spec fn vm_region_spec(&self) -> &Option<VirtualMemoryRegion> {
        &self.vm_region
    }

    pub closed spec fn shared_bit_spec(&self) -> u64 {
        self.shared_bit
    }

    pub closed spec fn private_bit_spec(&self) -> u64 {
        self.private_bit
    }

    pub closed spec fn pgtable_spec(&self) -> DekoPPtr<PageTable> {
        self.pgtable
    }

    pub closed spec fn kernel_mapping_spec(&self) -> MappingSpace {
        self.kernel_mapping
    }

    pub closed spec fn ctx_switch_stack_spec(&self) -> Option<DekoPPtr<DekoKernelStack>> {
        self.ctx_switch_stack
    }

    #[verifier::when_used_as_spec(shared_bit_spec)]
    #[inline]
    pub fn shared_bit(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.shared_bit_spec(),
    {
        self.shared_bit
    }

    #[verifier::when_used_as_spec(private_bit_spec)]
    #[inline]
    pub fn private_bit(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.private_bit_spec(),
    {
        self.private_bit
    }

    #[verifier::when_used_as_spec(kernel_mapping_spec)]
    #[inline]
    pub fn kernel_mapping(&self) -> (r: MappingSpace)
        requires
            self.wf(),
        ensures
            r == self.kernel_mapping_spec(),
    {
        self.kernel_mapping
    }

    #[verifier::when_used_as_spec(vm_region_spec)]
    #[inline]
    pub fn vm_region(&self) -> (r: &Option<VirtualMemoryRegion>)
        requires
            self.wf(),
        ensures
            r == self.vm_region_spec(),
    {
        &self.vm_region
    }

    #[verifier::when_used_as_spec(ctx_switch_stack_spec)]
    #[inline]
    pub fn ctx_switch_stack(&self) -> (r: Option<DekoPPtr<DekoKernelStack>>)
        requires
            self.wf(),
        ensures
            r == self.ctx_switch_stack_spec(),
    {
        self.ctx_switch_stack
    }

    #[inline]
    #[verifier::external_body]
    pub fn this_cpu() -> (r: (DekoPPtr<Self>, Tracked<DekoCpuCtxPermission>))
        ensures
            r.0@ == r.1@.ptr_perm().pptr(),
            r.0.addr() as u64 == PERCPU_BASE@,
            r.1@.wf_with(r.0),
    {
        // SAFETY: The PerCPU area is always mapped at the same virtual address, so
        // dereferencing a pointer to that address is safe. The PerCPU area is also
        // never freed, so using a static lifetime is safe as well.
        let (ptr, Tracked(ptr_perm)) = unsafe { DekoPPtr::<Self>::from_raw_uninit(PERCPU_BASE.0) };

        (ptr, Tracked::assume_new())
    }

    /// Creates a new CPU data structure.
    pub fn new(
        pgtable: DekoPPtr<PageTable>,
        shared_area: DekoPPtr<PerCpuShared>,
        ghcb: DekoPPtr<GuestHostCommucationBlock>,
        cpu_id: u64,
        shared_bit: u64,
        private_bit: u64,
        kernel_mapping: MappingSpace,
        vm_region: Option<VirtualMemoryRegion>,
        ctx_switch_stack: Option<DekoPPtr<DekoKernelStack>>,
    ) -> (r: Self)
        requires
            cpu_id < CPUID_MAX_COUNT as u64,
        ensures
            r.wf(),
    {
        broadcast use deko_std::array::lemma_sized_t_makes_sized_array;

        DekoCpuCtx {
            magic: CPU_AREA_MAGIC,
            ghcb,
            tss: X86Tss {
                reserved0: 0,
                stacks: Array::fill(0),
                _reserved1: 0,
                ist_stacks: Array::fill(0),
                _reserved2: 0,
                _reserved3: 0,
                io_bmp_base: 0,
            },
            pgtable,
            shared_area,
            cpu_id,
            private_bit,
            shared_bit,
            kernel_mapping,
            vm_region,
            ctx_switch_stack,
        }
    }

    #[verifier::external_body]
    fn as_ptr(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.addr(),
            PTE_BASE@ + ((r & 0x0000_FFFF_FFFF_F000u64) >> 9)
                <= 0x0000_FFFF_FFFF_FFFFu64
            // todo: add something to ensure the address is valid.
            ,
    {
        self as *const DekoCpuCtx as u64
    }

    #[verifier::external_body]
    pub fn map_shared_page(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut DekoCpuCtxPermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
    )
        requires
            vaddr.wf(),
            vaddr@ % 0x1000 == 0,
            old(perm).wf_with(ptr),
            ms == old(perm).pgtable_perm.mapping_space,
        ensures
            perm.wf_with(ptr),
    {
        let page: DekoPPtr<crate::mm::paging::Page> = ptr.borrow(Tracked(&perm.ptr_perm)).pgtable;
        let private_bit = ptr.borrow(Tracked(&perm.ptr_perm)).private_bit;
        let shared_bit = ptr.borrow(Tracked(&perm.ptr_perm)).shared_bit;

        PageTable::set_shared_4k(
            page,
            Tracked(&mut perm.pgtable_perm),
            vaddr,
            ms,
            private_bit,
            shared_bit,
        );
    }

    #[verifier::external_body]
    pub fn map_page_4k(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut DekoCpuCtxPermission>,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PteFlags,
    )
        requires
            vaddr.wf(),
            paddr.wf(),
            vaddr@ % 0x1000 == 0,
            paddr@ % 0x1000 == 0,
            old(perm).wf_with(ptr),
        ensures
            perm.pgtable_perm.private_bit == old(perm).pgtable_perm.private_bit,
            perm.pgtable_perm.shared_bit == old(perm).pgtable_perm.shared_bit,
            perm.wf_with(ptr),
            perm.pgtable_perm.virt_to_frame_spec(vaddr) matches Some(frame) && frame.address_spec(
                old(perm).pgtable_perm.private_bit,
                old(perm).pgtable_perm.shared_bit,
            ) == paddr,
    {
        let this = ptr.borrow(Tracked(&perm.ptr_perm));
        let page = this.pgtable;
        let private_bit = this.private_bit;
        let shared_bit = this.shared_bit;
        let ms = &this.kernel_mapping;

        PageTable::map_page_4k(
            page,
            Tracked(&mut perm.pgtable_perm),
            vaddr,
            paddr,
            ms,
            flags,
            private_bit,
            shared_bit,
        );
    }

    pub closed spec fn cpu_id(&self) -> u64 {
        self.cpu_id
    }

    pub closed spec fn ghcb_spec(&self) -> DekoPPtr<GuestHostCommucationBlock> {
        self.ghcb
    }

    // When possible, define all these getter and setter by macros.
    #[verifier::when_used_as_spec(ghcb_spec)]
    #[inline]
    pub fn ghcb(&self) -> (r: DekoPPtr<GuestHostCommucationBlock>)
        ensures
            r == self.ghcb_spec(),
    {
        self.ghcb
    }

    pub open spec fn is_valid_pgtable_request(&self, pgperm: &DekoPointsTo<PageTable>) -> bool {
        &&& pgperm.is_init()
    }

    pub fn pgtable(&self) -> (r: DekoPPtr<PageTable>)
        requires
            self.wf(),
        ensures
            r == self.pgtable_spec(),
    {
        self.pgtable
    }
}

/// This function is unsafe because the CPUID table address is provided by IGVM.
/// We cannot guaarantee that it is indeed valid. Also please note that the
/// address is 32bit as we do not have yet set up proper paging.
#[verifier::external_body]
#[inline(always)]
pub unsafe fn register_cpuid_table(addr: u32) -> (r: &'static CpuidTable)
    requires
        addr % 0x1000 == 0,
        addr != 0,
    ensures
        r.wf(),
{
    &*(addr as *const CpuidTable)
}

} // verus!
