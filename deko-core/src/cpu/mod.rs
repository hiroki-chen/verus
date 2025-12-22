pub mod apic;
pub mod ctx;
pub mod gdt;
pub mod idt;
pub mod idt_handlers;
pub mod irq;
pub mod msr;
pub mod regs;
pub mod smp;
pub mod task;
pub mod types;

use deko_macros::DekoDebug;
use deko_std::prelude::*;
use task::DekoRunnablePtr;
use vstd::atomic::{PAtomicBool, PAtomicU32, PermissionBool, PermissionU32};
use vstd::cell::{PCell, PointsTo};
use vstd::prelude::*;

use crate::cpu::apic::X86Apic;
use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::regs::read_cr3;
use crate::cpu::task::{
    DekoRunQueue, DekoRunQueuePermission, DekoRunQueuePred, DekoRunnable, DekoRunnablePred,
    DekoTaskArgs,
};
use crate::imp::ghcb::current_ghcb;
use crate::imp::RmpFlags;
use crate::mm::paging::{
    bit_not_in_addr_region, bit_not_overlapping, index_at_level_spec, Mapping, Page, PageTable,
    PageTablePath, PageTablePermission, PteFlags, RECURSIVE_INDEX,
};
use crate::mm::stack::{DekoIstStack, DekoKernelStack};
use crate::mm::vm::{
    VirtualMemory, VirtualMemoryRegion, VirtualMemoryRegionPermission, VirtualMemoryTemporary,
    VmMapping, VmMappingPred, VMR_GRANULE,
};
use crate::mm::{virt_to_phys, virt_to_phys_checked, DEKO_FRAME_ALLOCATOR};
use crate::snp::ghcb::GuestHostCommucationBlock;
use crate::snp::vmsa::{VmsaInitialContext, VmsaPage, VmsaPagePermission, VmsaPagePred};
use crate::snp::Rmp_ALL_BITS;
use crate::{die, kerror, kinfo, kpanic_if, kunimplemented, kwarn};

verus! {

pub const IST_DF: usize = 0;

pub const CPUID_MAX_COUNT: usize = 32;

pub const CPU_AREA_MAGIC: u64 = 0x114514;

pub struct GuestVmsaRef {
    pub vmsa: Option<PhysAddr>,
    pub caa: Option<PhysAddr>,
    pub generation: u64,
    pub gen_in_use: u64,
}

impl WellFormed for GuestVmsaRef {
    open spec fn wf(&self) -> bool {
        &&& self.vmsa matches Some(p) ==> p.wf()
        &&& self.caa matches Some(p) ==> p.wf()
    }
}

#[repr(C, packed(4))]
#[derive(DekoDebug)]
pub struct X86Tss {
    pub reserved0: u32,
    pub stacks: Array<u64, 3>,
    pub _reserved1: u64,
    pub ist_stacks: Array<u64, 7>,
    pub _reserved2: u64,
    pub _reserved3: u16,
    pub io_bmp_base: u16,
}

#[derive(DekoDebug)]
pub struct PerCpuShared {
    pub apic_id: u32,  // the id of the local apic
    pub cpu_index: usize,
    #[deko(skip)]
    pub guest_vmsa: DekoSimpleRwLock<GuestVmsaRef>,
    #[deko(skip)]
    pub online: (PAtomicBool, Tracked<PermissionBool>),
    #[deko(skip)]
    pub ipi_irr: Array<(PAtomicU32, Tracked<PermissionU32>), 8>,
    #[deko(skip)]
    pub ipi_pending: (PAtomicBool, Tracked<PermissionBool>),
    #[deko(skip)]
    pub nmi_pending: (
        PAtomicBool,
        Tracked<PermissionBool>,
    ),
    // ipi_state: IpiState, todo
}

impl WellFormed for PerCpuShared {
    open spec fn wf(&self) -> bool {
        &&& self.apic_id == self.cpu_index
        &&& self.cpu_index < CPUID_MAX_COUNT
        &&& self.guest_vmsa.wf()
        &&& self.online.1@.is_for(self.online.0)
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

    pub const fn new(id: u32) -> (r: Self)
        requires
            id < CPUID_MAX_COUNT,
        ensures
            r.wf(),
    {
        let online = PAtomicBool::new(false);
        let ipi_pending = PAtomicBool::new(false);
        let nmi_pending = PAtomicBool::new(false);
        let ipi_irr = Self::new_ipi_irr();
        let guest_vmsa = DekoSimpleRwLock::new_simple(
            GuestVmsaRef { vmsa: None, caa: None, generation: 0, gen_in_use: 0 },
        );

        proof {
            use_type_invariant(&guest_vmsa);
        }

        PerCpuShared {
            apic_id: id,
            cpu_index: id as usize,
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

impl RwLockPredicate<DekoAtomicDataNoPerm<PerCpuAreas>> for PerCpuAreasInv {
    open spec fn inv(self, v: DekoAtomicDataNoPerm<PerCpuAreas>) -> bool {
        &&& v.data.wf()
        &&& forall|i: int|
            #![trigger v.data.0@[i]]
            0 <= i < CPUID_MAX_COUNT as int ==> {
                &&& v.data.0@[i].wf()
                &&& v.data.0@[i].apic_id as int == i
            }
    }
}

impl PerCpuAreas {
    #[verifier::external_body]
    pub const fn new() -> (r: Self)
        ensures
            r.wf(),
            forall|i: int|
                #![trigger r.0@[i]]
                0 <= i < r.0@.len() ==> {
                    &&& r.0@[i].wf()
                    &&& r.0@[i].apic_id as int == i
                },
    {
        seq_macro::seq!(
            N in 0..32 {
                PerCpuAreas(Array::new(
                    [
                        #(
                            const { PerCpuShared::new(N) },
                        )*
                    ]
                ))
            }
        )
    }
}

impl View for PerCpuAreas {
    type V = Seq<PerCpuShared>;

    open spec fn view(&self) -> Self::V {
        self.0@
    }
}

/// This is a global list of per-cpu areas. Although we can implement this in
/// a lock-free but this would otherwise create a lot of complexity.
///
/// For verification and the ease of implementation, we just use a simple
/// read-write lock to protect the access to this structure.
pub exec static PERCPU_AREAS: DekoRwLock<PerCpuAreas, (), PerCpuAreasInv>
    ensures
        PERCPU_AREAS.wf(),
{
    let lock = DekoRwLock::new(
        DekoAtomicDataNoPerm::new(PerCpuAreas::new()),
        (),
        Ghost(PerCpuAreasInv {  }),
    );
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
    pub ghcb: DekoPPtr<GuestHostCommucationBlock>,
    pub tss: X86Tss,
    /// The page table of this CPU.
    pub pgtable: DekoPPtr<PageTable>,
    /// The stack for doing context switches.
    pub ctx_switch_stack: Option<VirtAddr>,
    /// The stack for handling interrupts.
    pub ist_stack: Option<DekoIstStack>,
    // /// The current stack.
    // pub current_stack: ...
    /// The private bit of the PTE of this core.
    #[deko(hex)]
    pub private_bit: u64,
    /// The shared bit of the PTE of this core.
    #[deko(hex)]
    pub shared_bit: u64,
    /// The high-level kernel mapping context for this CPU.
    pub kernel_mapping: MappingSpace,
    /// The virtual memory region used for per-cpu area.
    /// At stage2 this is [`Option::None`].
    pub vm_region: Option<VirtualMemoryRegion>,
    /// APIC interface for this CPU.
    pub apic: X86Apic,
    /// Runqueue
    pub run_queue: Option<DekoRwLock<DekoRunQueue, DekoRunQueuePermission, DekoRunQueuePred>>,
    /// Temporary mapping.
    pub temp_mapping: VirtualMemoryTemporary,
    /// The VMSA.
    pub deko_vmsa: DekoOnceCell<VmsaPage, VmsaPagePermission, VmsaPagePred>,
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
        &&& self.vm_region_perm matches Some(perm) ==> {
            &&& perm.pgtable_perm.private_bit == self.pgtable_perm.private_bit
            &&& perm.pgtable_perm.shared_bit == self.pgtable_perm.shared_bit
        }
        &&& self.ghcb_perm.is_init()
        &&& self.ghcb_perm.wf()
        &&& self.ghcb_perm.pptr() == self.ptr_perm.value().ghcb_spec()@
    }
}

#[repr(C, packed)]
#[derive(Clone, Copy, DekoDebug)]
pub struct CpuidFn {
    #[deko(hex)]
    pub eax_in: u32,
    #[deko(hex)]
    pub ecx_in: u32,
    #[deko(hex)]
    pub xcr0_in: u64,
    #[deko(hex)]
    pub xss_in: u64,
    #[deko(hex)]
    pub eax_out: u32,
    #[deko(hex)]
    pub ebx_out: u32,
    #[deko(hex)]
    pub ecx_out: u32,
    #[deko(hex)]
    pub edx_out: u32,
    #[deko(skip)]
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
#[derive(DekoDebug, Clone)]
pub struct CpuidTable {
    pub count: u32,
    #[deko(skip)]
    pub reserved_1: u32,
    #[deko(skip)]
    pub reserved_2: u64,
    #[deko(hex)]
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
    open spec fn wf(&self) -> bool {
        &&& self.stacks.wf()
        &&& self.ist_stacks.wf()
    }
}

impl WellFormed for DekoCpuCtx {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.tss.wf()
        &&& self.deko_vmsa.wf()
        &&& self.cpu_id < CPUID_MAX_COUNT as u64
        &&& self.magic == CPU_AREA_MAGIC
        &&& self.temp_mapping.wf()
    }
}

impl X86Tss {
    /// Set the IST stack pointer for the given index.
    #[verifier::external_body]
    pub fn set_ist_stack(&self, index: usize, stack_top: VirtAddr)
        requires
            index < 7,
            stack_top.wf(),
        ensures
            self.wf(),
    {
        unsafe {
            // The target address might be unaligned and we cannot
            // use any safe Rust code here.
            core::arch::asm!(
                "movq {0}, ({1})",
                in(reg) stack_top.0,
                in(reg) core::ptr::addr_of!(self.ist_stacks.0[index]),
                options(att_syntax),
            )
        }
    }
}

#[verus_verify]
impl DekoCpuCtx {
    uninterp spec fn addr(&self) -> u64;

    pub open spec fn vm_region_spec(&self) -> &Option<VirtualMemoryRegion> {
        &self.vm_region
    }

    pub open spec fn temp_mapping_spec(&self) -> &VirtualMemoryTemporary {
        &self.temp_mapping
    }

    pub open spec fn shared_bit_spec(&self) -> u64 {
        self.shared_bit
    }

    pub open spec fn private_bit_spec(&self) -> u64 {
        self.private_bit
    }

    pub open spec fn pgtable_spec(&self) -> DekoPPtr<PageTable> {
        self.pgtable
    }

    pub open spec fn kernel_mapping_spec(&self) -> MappingSpace {
        self.kernel_mapping
    }

    pub open spec fn ctx_switch_stack_spec(&self) -> Option<VirtAddr> {
        self.ctx_switch_stack
    }

    pub open spec fn apic_spec(&self) -> &X86Apic {
        &self.apic
    }

    pub open spec fn run_queue_spec(&self) -> Option<
        &DekoRwLock<DekoRunQueue, DekoRunQueuePermission, DekoRunQueuePred>,
    > {
        match &self.run_queue {
            Some(rq) => Some(rq),
            None => None,
        }
    }

    #[verifier::when_used_as_spec(apic_spec)]
    #[inline]
    pub fn apic(&self) -> (r: &X86Apic)
        requires
            self.wf(),
        ensures
            r == self.apic_spec(),
    {
        &self.apic
    }

    #[verifier::when_used_as_spec(temp_mapping_spec)]
    #[inline]
    pub fn temp_mapping(&self) -> (r: &VirtualMemoryTemporary)
        requires
            self.wf(),
        ensures
            r == self.temp_mapping_spec(),
        opens_invariants none
        no_unwind
    {
        &self.temp_mapping
    }

    #[verifier::when_used_as_spec(shared_bit_spec)]
    #[inline]
    pub fn shared_bit(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.shared_bit_spec(),
        opens_invariants none
        no_unwind
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
        opens_invariants none
        no_unwind
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
        opens_invariants none
        no_unwind
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
    pub fn ctx_switch_stack(&self) -> (r: Option<VirtAddr>)
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
        opens_invariants none
        no_unwind
    {
        // SAFETY: The PerCPU area is always mapped at the same virtual address, so
        // dereferencing a pointer to that address is safe. The PerCPU area is also
        // never freed, so using a static lifetime is safe as well.
        let (ptr, Tracked(ptr_perm)) = unsafe { DekoPPtr::<Self>::from_raw_uninit(PERCPU_BASE.0) };

        (ptr, Tracked::assume_new())
    }

    // #[inline]
    // #[verifier::when_used_as_spec(run_queue_spec)]
    // pub fn run_queue(&self) -> (r: Option<&DekoRunQueue>)
    //     requires
    //         self.wf(),
    //     ensures
    //         r == self.run_queue_spec(),
    // {
    //     match &self.run_queue {
    //         Some(rq) => {
    //         }
    //         None => None,
    //     }
    // }
    /// Creates a new CPU data structure.
    pub fn new(
        pgtable: DekoPPtr<PageTable>,
        ghcb: DekoPPtr<GuestHostCommucationBlock>,
        cpu_id: u64,
        shared_bit: u64,
        private_bit: u64,
        kernel_mapping: MappingSpace,
        vm_region: Option<VirtualMemoryRegion>,
        ctx_switch_stack: Option<VirtAddr>,
        ist_stack: Option<DekoIstStack>,
        run_queue: Option<DekoRwLock<DekoRunQueue, DekoRunQueuePermission, DekoRunQueuePred>>,
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
            cpu_id,
            private_bit,
            shared_bit,
            kernel_mapping,
            vm_region,
            ctx_switch_stack,
            ist_stack,
            apic: X86Apic {  },
            run_queue,
            temp_mapping: VirtualMemoryTemporary::new_zeroed(),
            deko_vmsa: DekoOnceCell::new(Ghost(VmsaPagePred {  })),
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

    /// Different from [`Self::allocate_deko_vmsa`] which allocates the VMSA for Deko's own
    /// use, this function allocates a VMSA for the guest for context switches, hypercalls,
    /// etc.
    pub fn allocate_guest_vmsa(ptr: DekoPPtr<Self>, Tracked(perm): Tracked<&mut DekoPointsTo<Self>>)
        requires
            old(perm).wf(),
            old(perm).pptr() == ptr@,
            old(perm).is_init(),
        ensures
            perm.wf(),
            perm.pptr() == ptr@,
    {
        kunimplemented!("stub")
        // Alternative interrupt injection configuration.

    }

    /// Allocates a VMSA for the given entry point.
    pub fn allocate_deko_vmsa(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut DekoCpuCtxPermission>,
        entry: u64,
    ) -> (r: (PhysAddr, u64))
        requires
            old(perm).wf_with(ptr),
            old(perm).ptr_perm.value().ctx_switch_stack is Some,
        ensures
            perm.wf_with(ptr),
    {
        // Check if we have already allocated the VMSA.
        {
            let cpu_borrow = ptr.borrow(Tracked(&perm.ptr_perm));
            if cpu_borrow.deko_vmsa.get().is_some() {
                kwarn!("VMSA already allocated for CPU {}", cpu_borrow.cpu_id);
            }
        }

        proof_decl! {
            let tracked mut vmsa_perm: VmsaPagePermission;
        }

        broadcast use crate::snp::RmpFlags::lemma_each_bit_is_valid;

        let flags = RmpFlags::vmpl1();
        proof {
            assert(flags.bits() & Rmp_ALL_BITS == flags.bits()) by {
                bit_u64_and_auto();
            }
        }

        let cpu_borrow = ptr.borrow(Tracked(&perm.ptr_perm));
        let private_bit = cpu_borrow.private_bit;
        let shared_bit = cpu_borrow.shared_bit;

        #[verus_spec(with Tracked(&mut perm.pgtable_perm) => Tracked(vmsa_perm))]
        let vmsa = VmsaPage::alloc(flags);

        proof {
            assert(perm.pgtable_perm.wf());
        }

        let Some(paddr) = virt_to_phys_checked(
            private_bit,
            shared_bit,
            VirtAddr::new(vmsa.page.addr() as u64),
            Tracked(&perm.pgtable_perm),
        ) else {
            kerror!("Failed to get physical address for VMSA allocation");
            die("VMSA physical address translation failed");
        };

        // This is problematic; we cannot have a fallback here.
        let Some(cr3) = virt_to_phys_checked(
            private_bit,
            shared_bit,
            cpu_borrow.pgtable.into_vaddr(),
            Tracked(&perm.pgtable_perm),
        ) else {
            kerror!("Failed to get CR3 for VMSA initialization");
            die("CR3 physical address translation failed");
        };

        // Now we need to initialize the VMSA.
        let init_ctx = VmsaInitialContext::new_with(
            entry,
            cpu_borrow.ctx_switch_stack.as_ref().unwrap().0,
            cr3.0,
            &cpu_borrow.tss,
        );

        // Check if stack is mapped?
        {
            let rsp = init_ctx.rsp;
            assume(perm.pgtable_perm.walk_requires(
                cpu_borrow.pgtable,
                VirtAddr(rsp),
                &cpu_borrow.kernel_mapping,
                private_bit,
                shared_bit,
            ));
            let mapping = PageTable::walk(
                cpu_borrow.pgtable,
                Tracked(&perm.pgtable_perm),
                VirtAddr(rsp),
                &cpu_borrow.kernel_mapping,
                private_bit,
                shared_bit,
            );

            kinfo!("VMSA stack mapping check: RSP", rsp => hex, "used for VMSA at CPU {}", cpu_borrow.cpu_id, "mapping:", mapping);
        }

        #[verus_spec(with Tracked(&mut vmsa_perm))]
        let sev_features = vmsa.init_from(&init_ctx);
        cpu_borrow.deko_vmsa.init(DekoAtomicData::new_with(vmsa, Tracked(vmsa_perm)));

        (paddr, sev_features)
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

    pub open spec fn cpu_id(&self) -> u64 {
        self.cpu_id
    }

    pub open spec fn ghcb_spec(&self) -> DekoPPtr<GuestHostCommucationBlock> {
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
        opens_invariants none
        no_unwind
    {
        self.pgtable
    }

    pub fn set_ist_stack_tss(&self, index: usize, stack_top: VirtAddr)
        requires
            self.wf(),
            index < 7,
            stack_top.wf(),
    {
        self.tss.set_ist_stack(index, stack_top);
    }

    /// Sets up a new CPU context.
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
    ensures
        cpu_perm@.wf_with(r),
        cpu_perm@.ptr_perm().value().ctx_switch_stack is Some,
        cpu_perm@.ptr_perm().value().run_queue is Some,
        cpu_perm@.ptr_perm().value().vm_region is Some

)]
    #[verifier::external_body]  // this function times out.
    pub fn setup_cpu(
        init_pgtable: DekoPPtr<PageTable>,
        private_bit: u64,
        shared_bit: u64,
        kernel_mapping: MappingSpace,
        id: u64,
    ) -> DekoPPtr<DekoCpuCtx> {
        broadcast use PteFlags::lemma_each_bit_is_valid;
        broadcast use PteFlags::lemma_from_bits_single;
        broadcast use VirtAddr::lemma_page_size_eq_shifts;
        broadcast use VirtAddr::lemma_page_shift_le_max;
        broadcast use VirtAddr::lemma_pfn_roundtrip;
        // We first allocate a new CPU context for.

        let (cpu_ctx_ptr, Tracked(ctx_perm)) = boxed_ptr!(DekoCpuCtx, &DEKO_FRAME_ALLOCATOR.0);
        let (ghcb, Tracked(ghch_perm)) =
            boxed_ptr!(GuestHostCommucationBlock, &DEKO_FRAME_ALLOCATOR.0);

        // First step is to map itself.
        let vaddr = cpu_ctx_ptr.into_vaddr();
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
            assert(0xFFFFFF8000000000 as u64 % PAGE_SIZE == 0 && 0xFFFFFF0000000000 as u64
                % PAGE_SIZE == 0) by (bit_vector);
            bit_u64_and_auto();
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
        let mapping = {
            let mapping = VmMapping::PhysMem { paddr, size: PAGE_SIZE };

            proof {
                assume(mapping.wf());
            }

            let arc = DekoRwLock::new(
                DekoAtomicData::new_with(mapping, Tracked(())),
                (),
                Ghost(VmMappingPred {  }),
            );

            proof {
                use_type_invariant(&arc);
            }

            DekoArc::new(
                DekoAtomicData::new(arc),
                &DEKO_FRAME_ALLOCATOR.0,
                Ghost(DekoSimpleRwLockPred {  }),
            )
        };

        proof {
            use_type_invariant(&mapping);
        }

        proof_with!(Ghost(&vm_region) => Tracked(vm_block_for_cpu_perm));
        let vm_block_for_self = VirtualMemory::new(
            VirtAddr(cpu_start.0)..VirtAddr(cpu_start.0 + PAGE_SIZE),
            mapping,
            cpu_self_flags,
        );

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
            assume(vm_region.compatible_spec(&vm_block_for_self));
            assume(vm_region.disjoint_blocks(&vm_block_for_self));
            bit_u64_and_auto();
        }

        // There are some proofs. Insert into the region.
        proof_with!(Tracked(&mut vm_perm), Tracked(vm_block_for_cpu_perm));
        vm_region.insert_at_vaddr(PERCPU_BASE, vm_block_for_self);

        // This is for the current context switch stack.
        let (cpu_css_stack, top_of_the_css_stack) = {
            let mut stack = DekoKernelStack::new_with_size(0x8000, false);
            stack.alloc_pages(private_bit, shared_bit, &DEKO_FRAME_ALLOCATOR);
            let top_of_the_stack = VirtAddr(stack.stack_top() + CONTEXT_SWITCH_STACK.0);
            let stack = VmMapping::Stack { stack };

            proof {
                assert(stack.mapping_size_spec() >= PAGE_SIZE) by {
                    assert(0x8000u64 >> 12 == 8) by (bit_vector);
                }
            }
            let arc = DekoRwLock::new(
                DekoAtomicData::new_with(stack, Tracked(())),
                (),
                Ghost(VmMappingPred {  }),
            );

            proof {
                use_type_invariant(&arc);
            }

            (
                DekoArc::new(
                    DekoAtomicData::new(arc),
                    &DEKO_FRAME_ALLOCATOR.0,
                    Ghost(DekoSimpleRwLockPred {  }),
                ),
                top_of_the_stack,
            )
        };

        // Create a new vm_block for the stack and then map it.
        proof {
            use_type_invariant(&cpu_css_stack);
        }

        proof_with!(Ghost(&vm_region) => Tracked(vm_block_for_stack_perm));
        let vm_block_for_stack = VirtualMemory::new(
            VirtAddr(top_of_the_css_stack.0 - 0x8000)..top_of_the_css_stack,
            cpu_css_stack,
            PteFlags::nx_kernel(),
        );

        proof {
            assume(vm_block_for_stack.wf());
            // The same proofs.
            assume(vm_region.compatible_spec(&vm_block_for_stack));
            assume(vm_region.disjoint_blocks(&vm_block_for_stack));
        }

        proof_with!(Tracked(&mut vm_perm), Tracked(vm_block_for_stack_perm));
        vm_region.insert_at_vaddr(VirtAddr(top_of_the_css_stack.0 - 0x8000), vm_block_for_stack);

        // Allocate a stack for interrupt service routines.
        let (ist_df_stack, top_of_ist_stack) = {
            let stack = DekoKernelStack::new_with_size(0x8000, false);
            let top_of_the_stack = VirtAddr(stack.stack_top() + STACK_IST_DF_BASE.0);
            let stack = VmMapping::Stack { stack };

            proof {
                assert(stack.mapping_size_spec() >= PAGE_SIZE) by {
                    assert(0x8000u64 >> 12 == 8) by (bit_vector);
                }
            }

            let arc = DekoRwLock::new(
                DekoAtomicData::new_with(stack, Tracked(())),
                (),
                Ghost(VmMappingPred {  }),
            );

            proof {
                use_type_invariant(&arc);
            }

            (
                DekoArc::new(
                    DekoAtomicData::new(arc),
                    &DEKO_FRAME_ALLOCATOR.0,
                    Ghost(DekoSimpleRwLockPred {  }),
                ),
                top_of_the_stack,
            )
        };

        proof_with!(Ghost(&vm_region) => Tracked(vm_block_for_ist_stack_perm));
        let vm_block_for_ist_stack = VirtualMemory::new(
            VirtAddr(top_of_ist_stack.0 - 0x8000)..top_of_ist_stack,
            ist_df_stack,
            PteFlags::nx_kernel(),
        );
        proof {
            assume(vm_block_for_ist_stack.wf());
            // The same proofs.
            assume(vm_region.compatible_spec(&vm_block_for_ist_stack));
            assume(vm_region.disjoint_blocks(&vm_block_for_ist_stack));
        }

        proof_with!(Tracked(&mut vm_perm), Tracked(vm_block_for_ist_stack_perm));
        vm_region.insert_at_vaddr(VirtAddr(top_of_ist_stack.0 - 0x8000), vm_block_for_ist_stack);

        // let cpu_ist_stack = DekoIstStack { df_stack: Some(cpu_ist_stack), df_ss: None };
        let (run_queue, Tracked(run_queue_perm)) = DekoRunQueue::new();
        let run_queue = DekoRwLock::new(
            DekoAtomicData::new_with(run_queue, Tracked(run_queue_perm)),
            (),
            Ghost(DekoRunQueuePred {  }),
        );

        let mut cpu_ctx = DekoCpuCtx::new(
            init_pgtable,
            ghcb,
            id,
            shared_bit,
            private_bit,
            kernel_mapping,
            Some(vm_region),
            Some(top_of_the_css_stack),
            // Some(cpu_ist_stack),
            None,
            // None,
            Some(run_queue),
        );

        cpu_ctx.temp_mapping.set(
            PERCPU_TEMP_BASE_4K,
            ((PERCPU_TEMP_END_4K.0 - PERCPU_TEMP_BASE_4K.0) / PAGE_SIZE) as usize,
        );

        cpu_ctx.set_ist_stack_tss(IST_DF, top_of_ist_stack);

        // Finally we write the CPU context to the memory.
        cpu_ctx_ptr.write(Tracked(&mut ctx_perm), cpu_ctx);

        // Something to be done with the permissions.
        // let cpu_ctx_perm = Tracked(DekoCpuCtxPermission {
        //     ptr_perm: ctx_perm,
        //     pgtable_perm: dummy_pgtable_perm(),
        //     ghcb_perm: ghch_perm,
        //     ctx_switch_stack_perm: Some(stack_perm),
        //     vm_region_perm: Some(vm_perm),
        // });
        proof_with!(|= Tracked::assume_new());
        cpu_ctx_ptr
    }

    /// Setup the idle task for this CPU.
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<DekoCpuCtxPermission>,
                -> new_perm: Tracked<DekoCpuCtxPermission>,
        requires
            perm.wf_with(ptr),
            perm.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
            perm.ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf(),
        ensures
            new_perm@.wf_with(ptr),
            new_perm@.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
            new_perm@.ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf(),
    )]
    pub fn setup_idle_task(ptr: DekoPPtr<Self>, entry: u64) {
        // Create a new idle task.
        proof_with!(Tracked(perm) => Tracked(new_perm));
        let task = DekoRunnable::new(
            ptr,
            DekoTaskArgs {
                parent: None,
                entry,
                name: "idle",
                mode: task::DekoTaskMode::Kernel {
                    entry,
                    param: 0,  // cpu id... etc.
                    ret: crate::cpu::task::run_kernel_tasks_func_ptr(),
                },
            },
        );

        // Now insert into the runqueue.
        let cpu_ctx = ptr.borrow(Tracked(&new_perm.ptr_perm));

        kpanic_if!(core::hint::unlikely(
            cpu_ctx.run_queue.is_none()),
            "Runqueue is not initialized for CPU",
            cpu_ctx.cpu_id,
        );

        let lock = cpu_ctx.run_queue.as_ref().unwrap();
        let mut write_handle = lock.acquire_write();
        let DekoAtomicData { data: mut runqueue, mut perm } = write_handle.get();

        kpanic_if!(core::hint::unlikely(runqueue.run_list.len() >= usize::MAX - 1),
            "Runqueue is full for CPU",
            cpu_ctx.cpu_id,
        );

        proof_with!(Tracked(perm.borrow_mut()));
        runqueue.set_idle_task(task);

        write_handle.release_write(DekoAtomicData::new_with(runqueue, perm));

        proof {
            use_type_invariant(&lock);
        }

        proof_with!(|= Tracked(new_perm));
        ()
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

/// Start an application processor given its per-cpu shared area.
///
/// This should be guarded behind `imp`
#[verus_spec()]
pub fn start_application_processor(which: &PerCpuShared) {
    kinfo!("Starting application processor: ", which.apic_id);

    let (bsp, Tracked(bsp_perm)) = DekoCpuCtx::this_cpu();
    let bsp = bsp.borrow(Tracked(&bsp_perm.ptr_perm));

    let cpu_entry = ap_start_func_ptr();
    // Also allocate a new page table for this cpu.
    let (init_pgtable, _, Tracked(pgtable_perm)) = PageTable::new(
        bsp.private_bit(),
        bsp.shared_bit(),
        Ghost(&bsp.kernel_mapping_spec()),
    );

    let old_pte_value = *bsp.pgtable.borrow(Tracked(&bsp_perm.pgtable_perm.pgtable_perm)).0.index(
        PGTABLE_LVL3_IDX_SHARED as usize,
    );

    // Copy the shared mappings from the kernel page table.
    PageTable::update_entry_by_ptr(
        init_pgtable,
        Tracked(&mut pgtable_perm.pgtable_perm),
        PGTABLE_LVL3_IDX_SHARED as usize,
        old_pte_value,
    );

    assume(pgtable_perm.wf());  // prove this later.

    // Allocate context for this cpu.
    proof_with!(Tracked(pgtable_perm) => Tracked(mut cpu_perm));
    let cpu_ctx = DekoCpuCtx::setup_cpu(
        init_pgtable,
        bsp.private_bit,
        bsp.shared_bit,
        bsp.kernel_mapping.clone(),
        which.apic_id as u64,
    );

    // Move below code into `crate::imp``.
    let (vmsa, sev_features) = DekoCpuCtx::allocate_deko_vmsa(
        cpu_ctx,
        Tracked(&mut cpu_perm),
        cpu_entry,
    );

    // Now invoke the ap creation routine.
    let (ghcb, Tracked(ghcb_perm)) = current_ghcb();
    kinfo!("ap_create arguments:");
    kinfo!("  ghcb: ", ghcb);
    kinfo!("  apic_id: ", which.apic_id);
    kinfo!("  vmsa: ", vmsa);
    kinfo!("  sev_features: ", sev_features);

    GuestHostCommucationBlock::ap_create(
        ghcb,
        Tracked(ghcb_perm),
        which.apic_id,
        sev_features,
        0,
        vmsa,
        1,
    );
}

/// Other APs will start execution from here.
#[allow(improper_ctypes_definitions)]
#[no_mangle]
#[verus_spec(
    with
        Tracked(ap_perm): Tracked<DekoCpuCtxPermission>,
)]
#[verifier::exec_allows_no_decreases_clause]
unsafe extern "C" fn ap_start() -> ! {
    // kinfo!("Application processor started."); // do not do this as ghcb is not shared yet.
    loop {
    }
}

func_ptr!(ap_start);

} // verus!
