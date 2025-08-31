pub mod gdt;
pub mod idt;
pub mod msr;
pub mod types;

use deko_std::prelude::*;
use vstd::atomic::{PAtomicBool, PAtomicU32, PermissionBool, PermissionU32};
use vstd::prelude::*;

use crate::address::{PhysAddr, VirtAddr};
use crate::mm::paging::PageTable;
use crate::snp::ghcb::GuestHostCommucationBlock;

verus! {

pub const CPUID_MAX_COUNT: usize = 128;

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
pub struct X86Tss {
    reserved0: u32,
    stacks: Array<u64, 3>,
    _reserved1: u64,
    ist_stacks: Array<u64, 7>,
    _reserved2: u64,
    _reserved3: u16,
    io_bmp_base: u16,
}

pub struct PerCpuShared {
    apic_id: u32,  // the id of the local apic
    cpu_index: usize,
    guest_vmsa: RwLockNoPred<GuestVmsaRef>,
    online: (PAtomicBool, Tracked<PermissionBool>),
    ipi_irr: Array<(PAtomicU32, Tracked<PermissionU32>), 8>,
    ipi_pending: (PAtomicBool, Tracked<PermissionBool>),
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

/// The structure that holds each core's own data.
pub struct CpuData {
    /// The GHCB block for this CPU.
    ghcb: OnceCellNoPred<GuestHostCommucationBlock>,
    tss: X86Tss,
    pgtable: DekoPPtr<PageTable>,
    pgtable_perm: Tracked<DekoPointsTo<PageTable>>,
    shared_area: DekoPPtr<PerCpuShared>,
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

impl WellFormed for CpuData {
    closed spec fn wf(&self) -> bool {
        &&& self.ghcb.wf()
        &&& self.tss.wf()
        &&& self.pgtable_perm.wf()
        &&& self.pgtable@ === self.pgtable_perm@.pptr()
    }
}

impl X86Tss {

}

impl CpuData {
    uninterp spec fn addr(&self) -> u64;

    /// Create a new CPU data structure.
    pub fn new(
        pgtable: DekoPPtr<PageTable>,
        pgtable_perm: Tracked<DekoPointsTo<PageTable>>,
        shared_area: DekoPPtr<PerCpuShared>,
    ) -> (r: Self)
        requires
            pgtable_perm.wf(),
            pgtable@ === pgtable_perm@.pptr(),
        ensures
            r.wf(),
    {
        CpuData {
            ghcb: OnceCellNoPred::new(Ghost(())),
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
            pgtable_perm,
            shared_area,
        }
    }

    #[verifier::external_body]
    fn as_ptr(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.addr(),
    {
        self as *const CpuData as u64
    }

    pub fn map_self_stage2(&self)
        requires
            self.wf(),
    {
        let vaddr = VirtAddr::from(self.as_ptr());
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
