pub mod apic;
pub mod ctx;
pub mod gdt;
pub mod idt;
pub mod idt_handlers;
pub mod ipi;
pub mod irq;
pub mod msr;
pub mod regs;
pub mod smp;
pub mod task;
pub mod tlb;
pub mod types;

use core::borrow::BorrowMut;
use core::panic;

use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::prelude::*;
use regs::{read_cr4, write_cr4};
use task::DekoRunnablePtr;
use vstd::atomic::{PAtomicBool, PAtomicU32, PermissionBool, PermissionU32};
use vstd::cell::{PCell, PointsTo};
use vstd::invariant;
use vstd::prelude::*;

use crate::collections::{get_unchecked, update_vec};
use crate::cpu::apic::{X86Apic, X86LocalApic, X86LocalApicPred};
use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::gdt::GlobalDescriptorTable;
use crate::cpu::ipi::{
    add_ipi_available_cpu, CpuIpiArea, CpuIpiAreaPermission, DekoIpIMessage, DekoIpiRequest,
};
use crate::cpu::irq::{
    raw_irq_enable, DekoSafeRwLock, DekoUnsafeRwLock, IrqSafeLockGuard, IrqState,
    IrqStatePermission, IrqUnSafeLockGuard,
};
use crate::cpu::regs::{read_cr3, sse_init, Cr4Flags};
use crate::cpu::task::{
    cpu_idle_func_ptr, schedule_init, DekoRunQueue, DekoRunQueuePermission, DekoRunQueuePred,
    DekoRunnable, DekoRunnablePred, DekoTaskArgs, DEKO_TASK_LIST,
};
use crate::guest::CaaArea;
use crate::imp::ghcb::{current_ghcb, msr_register_ghcb_gpa};
use crate::imp::{vmpl1_cpuid, RmpFlags, VMPL_GUEST_DEKO_MONITOR};
use crate::mm::frame_allocator::DekoPageFrameBox;
use crate::mm::paging::{
    bit_not_in_addr_region, bit_not_overlapping, index_at_level_spec, Mapping, Page, PageTable,
    PageTablePath, PageTablePermission, PteFlags, RECURSIVE_INDEX,
};
use crate::mm::stack::{DekoIstStack, DekoKernelStack};
use crate::mm::vm::{
    make_mapping, VirtualMemory, VirtualMemoryRegion, VirtualMemoryRegionPermission,
    VirtualMemoryTemporary, VmMapping, VmMappingPred, VMR_GRANULE,
};
use crate::mm::{virt_to_phys, virt_to_phys_checked, DEKO_FRAME_ALLOCATOR_FULL};
use crate::policy::userapp::setup_vmpl1_func_ptr;
use crate::snp::doorbell::{HVDoorbell, HvDoorbellPtrPermission, HvDoorbellPtrPred};
use crate::snp::ghcb::{validate_ghcb, GuestHostCommunicationBlock};
use crate::snp::vmsa::{VmsaInitialContext, VmsaPage, VmsaPagePermission, VmsaPagePred, VMSA};
use crate::snp::{
    is_vmpl1, is_vmpl1_user, rmpadjust, rmpquery, Rmp_ALL_BITS, VMPL_GUEST_SECURE_APP,
};
use crate::{die, kdebug, kerror, kinfo, kpanic_if, kunimplemented, kwarn};

verus! {

pub struct CpuidTablePred;

impl Predicate<DekoAtomicData<CpuidTable, ()>> for CpuidTablePred {
    #[verifier::inline]
    open spec fn inv(self, data: DekoAtomicData<CpuidTable, ()>) -> bool {
        data.wf()
    }
}

pub exec static CPUID_TABLE: DekoOnceCell<CpuidTable, (), CpuidTablePred>
    ensures
        CPUID_TABLE.wf(),
{
    DekoOnceCell::new(Ghost(CpuidTablePred {  }))
}

pub const IST_DF: usize = 0;

pub const CPUID_MAX_COUNT: usize = 32;

pub const CPU_AREA_MAGIC: u64 = 0x114514;

pub exec static CPU_NUM: DekoOnceCell<DekoCpuNum, (), DekoCpuNumPred>
    ensures
        CPU_NUM.wf(),
{
    DekoOnceCell::new(Ghost(DekoCpuNumPred {  }))
}

impl WellFormed for DekoCpuNum {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& 1 <= self.num <= CPUID_MAX_COUNT as u64
    }
}

#[repr(transparent)]
#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub struct DekoCpuNum {
    pub num: u64,
}

#[inline]
#[verus_spec(
    requires
        1 <= num <= CPUID_MAX_COUNT as u64,
)]
pub fn set_availabe_cpu_nums(num: u64) {
    if CPU_NUM.get().is_some() {
        kwarn!("CPU_NUM is already set!");
        return ;
    }
    CPU_NUM.init(DekoAtomicData::new(DekoCpuNum { num }));

    proof_with!(=> Tracked(mut percpu_areas_perm));
    let mut percpu_areas = PerCpuAreas::new();

    for i in 0..num as u32
        invariant
            num <= CPUID_MAX_COUNT as u64,
            percpu_areas.wf_with(percpu_areas_perm),
            percpu_areas@.len() == i as int,
    {
        proof_with!(Tracked(&mut percpu_areas_perm));
        percpu_areas.push_new_cpu(i);
    }

    deko_rwlock_write_atomic_data!(
        PERCPU_AREAS,
        data,
        data_perm,
        {
            data = Some(percpu_areas);
            data_perm = Tracked(percpu_areas_perm);
        }
    );
}

with_atomic_pred!(
    DekoCpuNum,
    (),
    fields: { },
    perm_fields: { },
    data.wf()
);

#[derive(DekoDebug)]
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
    pub guest_vmsa: DekoSimpleRwLock<GuestVmsaRef, IrqUnSafeLockGuard>,
    #[deko(skip)]
    pub online: PAtomicBool,
    #[deko(skip)]
    pub ipi_irr: Array<PAtomicU32, 8>,
    #[deko(skip)]
    pub ipi_pending: PAtomicBool,
    #[deko(skip)]
    pub nmi_pending: PAtomicBool,
    /// A shared area for IPI handling; other CPUs
    /// can write to this area when sending IPIs.
    #[deko(skip)]
    pub ipi_shared: CpuIpiArea,
}

with_permission! {
    PerCpuShared,
    online_perm: PermissionBool,
    ipi_irr_perm: Seq<PermissionU32>,
    ipi_pending_perm: PermissionBool,
    nmi_pending_perm: PermissionBool,
    ipi_shared_perm: CpuIpiAreaPermission,
}

impl WellFormed for PerCpuShared {
    open spec fn wf(&self) -> bool {
        &&& self.apic_id == self.cpu_index
        &&& self.cpu_index < CPUID_MAX_COUNT
        &&& self.guest_vmsa.wf()
        &&& self.ipi_irr.wf()
        &&& forall|i: int| 0 <= i && i < 8 ==> #[trigger] self.ipi_irr@[i as int].wf()
    }
}

impl PerCpuShared {
    #[inline(always)]
    const fn new_ipi_irr() -> (r: (Array<PAtomicU32, 8>, Tracked<Seq<PermissionU32>>))
        ensures
            r.0.wf(),
            r.0@.len() == r.1@.len(),
            forall|i: int|
                #![trigger r.1@[i as int]]
                #![trigger r.0@[i as int]]
                0 <= i && i < 8 ==> {
                    &&& r.0@[i as int].wf()
                    &&& r.1@[i as int].is_for(r.0@[i as int])
                },
    {
        broadcast use deko_std::array::lemma_sized_t_makes_sized_array;

        let (arr, perms) =
            seq_macro::seq! {
            N in 0..8 {{
                #(
                    let (atomic~N, perm~N) = PAtomicU32::new(0);
                )*

                // Collect atomics into array
                let arr = Array::new([
                    #(atomic~N,)*
                ]);

                // Collect permissions into sequence
                let perms = Array::new([
                    #(perm~N,)*
                ]);

                (arr, perms)
            }}
        };

        let tracked perms_transformed = Seq::tracked_new(8, |i| perms@[i as int]@);

        (arr, Tracked(perms_transformed))
    }

    pub const fn new(id: u32) -> (r: (PerCpuShared, Tracked<PerCpuSharedPermission>))
        requires
            id < CPUID_MAX_COUNT,
        ensures
            r.0.apic_id == id,
            r.0.cpu_index == id as usize,
            r.0.wf(),
            r.1@.online_perm.is_for(r.0.online),
            r.1@.ipi_pending_perm.is_for(r.0.ipi_pending),
            r.1@.nmi_pending_perm.is_for(r.0.nmi_pending),
            r.1@.ipi_irr_perm.len() == 8,
            forall|i: int|
                #![trigger r.1@.ipi_irr_perm[i as int]]
                0 <= i < 8 ==> {
                    &&& r.0.ipi_irr@[i as int].wf()
                    &&& r.1@.ipi_irr_perm[i as int].is_for(r.0.ipi_irr@[i as int])
                },
            r.1@.ipi_shared_perm.pending_perm.is_for(r.0.ipi_shared.pending),
            r.1@.ipi_shared_perm.request_set_perm.is_for(r.0.ipi_shared.request_set),
            r.1@.ipi_shared_perm.handler_perm.id() == r.0.ipi_shared.handler.id(),
            r.1@.ipi_shared_perm.message_perm.id() == r.0.ipi_shared.message.id(),
            r.1@.ipi_shared_perm.handler_perm.is_init(),
            r.1@.ipi_shared_perm.message_perm.is_init(),
    {
        let (online, Tracked(online_perm)) = PAtomicBool::new(false);
        let (ipi_pending, Tracked(ipi_pending_perm)) = PAtomicBool::new(false);
        let (nmi_pending, Tracked(nmi_pending_perm)) = PAtomicBool::new(false);
        let (ipi_irr, Tracked(ipi_irr_perm)) = Self::new_ipi_irr();
        let guest_vmsa = DekoSimpleRwLock::new_simple(
            GuestVmsaRef { vmsa: None, caa: None, generation: 0, gen_in_use: 0 },
            IrqUnSafeLockGuard {  },
        );
        let (ipi_shared, Tracked(ipi_shared_perm)) = CpuIpiArea::new();

        proof {
            use_type_invariant(&guest_vmsa);
        }

        (
            PerCpuShared {
                apic_id: id,
                cpu_index: id as usize,
                guest_vmsa,
                online,
                ipi_irr,
                ipi_pending,
                nmi_pending,
                ipi_shared,
            },
            Tracked(
                PerCpuSharedPermission {
                    online_perm,
                    ipi_irr_perm,
                    ipi_pending_perm,
                    nmi_pending_perm,
                    ipi_shared_perm,
                },
            ),
        )
    }
}

/// A collection of globally shared area for CPUs to access each other's state.
///
/// This is implemented as a vector which requires dynamic allocator but this
/// is fine as this is only used after the kernel is fully booted (AP CPUs are
/// online) so we can use the normal kernel allocator.
#[derive(DekoDebug)]
pub struct PerCpuAreas(pub crate::collections::Vec<PerCpuShared>);

#[verus_verify]
impl PerCpuAreas {

}

with_permission! {
    PerCpuAreas,
    shared_perms: Seq<PerCpuSharedPermission>,
}

type PerCpuAreasOpt = Option<PerCpuAreas>;

with_atomic_pred!(
    PerCpuAreasOpt,
    PerCpuAreasPermission,
    fields: { },
    perm_fields: { },
    if data.is_some() {
        data.unwrap().wf_with(perm) && data.wf()
    } else {
        true
    }
);

impl WellFormed for PerCpuAreas {
    open spec fn wf(&self) -> bool {
        &&& self.0.wf()
        &&& forall|i: int|
            #![trigger self@[i as int]]
            0 <= i < self@.len() as int ==> {
                &&& self@[i as int].wf()
                &&& self@[i as int].cpu_index == i as usize
            }
    }
}

#[verus_verify]
impl PerCpuAreas {
    pub open spec fn wf_with(&self, perm: PerCpuAreasPermission) -> bool {
        &&& self.0@.len() <= CPUID_MAX_COUNT
        &&& self.0@.len() == perm.shared_perms.len()
        &&& self.wf()
        &&& forall|i: int|
            #![trigger perm.shared_perms[i as int]]
            0 <= i < self@.len() as int ==> {
                &&& self.wf()
                &&& self@[i as int].wf()
                &&& perm.shared_perms[i as int].online_perm.is_for(self@[i as int].online)
                &&& perm.shared_perms[i as int].ipi_pending_perm.is_for(self@[i as int].ipi_pending)
                &&& perm.shared_perms[i as int].nmi_pending_perm.is_for(self@[i as int].nmi_pending)
                &&& perm.shared_perms[i as int].ipi_irr_perm.len() == 8
                &&& forall|j: int|
                    0 <= j < 8 ==> {
                        #[trigger] perm.shared_perms[i as int].ipi_irr_perm[j as int].is_for(
                            self@[i as int].ipi_irr@[j as int],
                        )
                    }
                &&& perm.shared_perms[i as int].ipi_shared_perm.pending_perm.is_for(
                    self@[i as int].ipi_shared.pending,
                )
                &&& perm.shared_perms[i as int].ipi_shared_perm.request_set_perm.is_for(
                    self@[i as int].ipi_shared.request_set,
                )
                &&& perm.shared_perms[i as int].ipi_shared_perm.handler_perm.id()
                    == self@[i as int].ipi_shared.handler.id()
                &&& perm.shared_perms[i as int].ipi_shared_perm.message_perm.id()
                    == self@[i as int].ipi_shared.message.id()
                &&& perm.shared_perms[i as int].ipi_shared_perm.handler_perm.is_init()
                &&& perm.shared_perms[i as int].ipi_shared_perm.message_perm.is_init()
            }
    }

    /// Push a new CPU shared area into the collection.
    #[verus_spec(
        with
            Tracked(perm): Tracked<&mut PerCpuAreasPermission>,
        requires
            old(self).wf_with(*old(perm)),
            old(self)@.len() < CPUID_MAX_COUNT,
            id == old(self)@.len() as u32,
        ensures
            self.wf_with(*perm),
            self@.len() == old(self)@.len() + 1,
            self@.len() <= CPUID_MAX_COUNT,
    )]
    pub fn push_new_cpu(&mut self, id: u32) {
        let (cpu_shared, Tracked(cpu_shared_perm)) = PerCpuShared::new(id);

        self.0.push(cpu_shared);

        proof {
            perm.shared_perms.tracked_push(cpu_shared_perm);
        }
    }

    /// Create a new, empty [`PerCpuAreas`] structure.
    #[verus_spec(r =>
        with
            -> perm: Tracked<PerCpuAreasPermission>,
        ensures
            r.wf(),
            r@.len() == 0,
            r.wf_with(perm@),
    )]
    #[inline]
    pub fn new() -> PerCpuAreas {
        proof_with!(|= Tracked(PerCpuAreasPermission { shared_perms: Seq::tracked_empty() }));
        Self(crate::vec![])
    }
}

impl View for PerCpuAreas {
    type V = Seq<PerCpuShared>;

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        self.0@
    }
}

/// This is a global list of per-cpu areas. Although we can implement this in
/// a lock-free but this would otherwise create a lot of complexity.
///
/// For verification and the ease of implementation, we just use a simple
/// read-write lock to protect the access to this structure.
///
/// Because this struct is frequently accessed, it is unwise for use to allocate everything
/// just on the stack as this would cause a lot of stack overflows and bad for performance.
pub exec static PERCPU_AREAS: DekoSafeRwLock<
    Option<PerCpuAreas>,
    PerCpuAreasPermission,
    PerCpuAreasOptPred,
>
    ensures
        PERCPU_AREAS.wf(),
{
    let lock = DekoRwLock::new(
        DekoAtomicData::new_with(
            None,
            Tracked(PerCpuAreasPermission { shared_perms: Seq::tracked_empty() }),
        ),
        IrqSafeLockGuard {  },
        Ghost(PerCpuAreasOptPred {  }),
    );
    proof {
        use_type_invariant(&lock);
    }

    lock
}

/// Per-VMPL extended context for each CPU core.
#[derive(DekoDebug)]
pub struct DekoCpuCtxPerVmpl {
    /// The VMPL level of this extended context.
    pub vmpl: u8,
    /// The VMSA for this extended context.
    pub vmsa: VmsaPage,
    /// The GHCB for this extended context.
    pub ghcb: DekoPPtr<GuestHostCommunicationBlock>,
    /// The gpa of the GHCB for this extended context.
    pub ghcb_gpa: PhysAddr,
    /// The doorbell for this extended context to use.
    pub doorbell: DekoUnsafeRwLock<
        DekoPPtr<HVDoorbell>,
        HvDoorbellPtrPermission,
        HvDoorbellPtrPred,
    >,
    /// The physical address of the doorbell.
    pub doorbell_pa: PhysAddr,
    /// The stack for this extended context.
    pub vmpl1_stack: VirtAddr,
    /// The TSS.
    pub tss: DekoPPtr<X86Tss>,
    /// The GDT.
    pub gdt: DekoPPtr<GlobalDescriptorTable>,
    /// The task currently loaded in this per-CPU VMPL1 runtime slot.
    pub current_pid: Option<u32>,
    /// Whether the runtime slot contains task state that has not yet been
    /// exported back into the per-task shadow record.
    pub slot_dirty: bool,
    /// Pending synchronous export request issued by another CPU.
    pub pending_export_pid: Option<u32>,
    /// Target CPU for the pending synchronous export request.
    pub pending_export_target_cpu: Option<u32>,
    /// Version requested by the importing CPU for this export.
    pub pending_export_version: u64,
    /// Last export version acknowledged by this CPU for the current slot.
    pub last_export_ack_version: u64,
    /// The nested IRQ.
    #[deko(skip)]
    pub nested_irq: IrqState,
    /// Deferred VMPL1 timer event request. Set in doorbell handling and
    /// consumed from non-IRQ context.
    pub deferred_timer_event: bool,
    /// Guard bit set while VMPL1 is issuing a syscall VMPL switch.
    pub syscall_switch_in_progress: bool,
    /// Last TSC when VMPL1 timer notification was forwarded to VMPL0.
    pub last_timer_notify_tsc: u64,
}

with_permission! {
    DekoCpuCtxPerVmpl,
    vmsa_perm: VmsaPagePermission,
    ghcb_perm: DekoPointsTo<GuestHostCommunicationBlock>,
    nested_irq_perm: IrqStatePermission,
}

impl WellFormed for DekoCpuCtxPerVmpl {
    open spec fn wf(&self) -> bool {
        &&& self.vmpl < 4
        &&& self.vmsa.wf()
        &&& self.doorbell.wf()
        &&& self.doorbell_pa@ % PAGE_SIZE == 0
        &&& self.pending_export_pid is Some <==> self.pending_export_target_cpu is Some
    }
}

#[verus_verify]
impl DekoCpuCtxPerVmpl {
    pub open spec fn wf_with(&self, perm: DekoCpuCtxPerVmplPermission) -> bool {
        &&& perm.vmsa_perm.ptr_perm.pptr() == self.vmsa.page@
        &&& perm.vmsa_perm.ptr_perm.is_init()
        &&& perm.vmsa_perm.ptr_perm.wf()
        &&& perm.ghcb_perm.pptr() == self.ghcb@
        &&& perm.ghcb_perm.is_init()
        &&& perm.ghcb_perm.wf()
        &&& perm.nested_irq_perm.wf_with(&self.nested_irq)
    }

    /// Create a new [`DekoCpuCtxPerVmpl`] structure with dummy VMSA and GHCB.
    ///
    /// Note that we will not register the VMSA nor GHCB here. The caller must
    /// ensure that they will be later registered before use.
    #[verus_spec(r =>
        with
            Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
            -> perm: Tracked<DekoCpuCtxPerVmplPermission>,
        requires
            vmpl < 4,
            old(pgtable_perm).wf(),
            private_bit == old(pgtable_perm).private_bit,
            shared_bit == old(pgtable_perm).shared_bit,
        ensures
            r.wf(),
            r.wf_with(perm@),
            r.current_pid is None,
            pgtable_perm.wf(),
            pgtable_perm.pgtable_perm == old(pgtable_perm).pgtable_perm,
            pgtable_perm.private_bit == old(pgtable_perm).private_bit,
            pgtable_perm.shared_bit == old(pgtable_perm).shared_bit,
            pgtable_perm.mapping_space == old(pgtable_perm).mapping_space,
    )]
    pub fn new(vmpl: u8, private_bit: u64, shared_bit: u64) -> Self {
        broadcast use RmpFlags::lemma_each_bit_is_valid;

        proof {
            bit_u32_and_auto();
        }

        proof_with!(Tracked(pgtable_perm) => Tracked(vmsa_perm));
        let vmsa = VmsaPage::alloc(RmpFlags::vmpl1());

        // Allocate a new GHCB.
        let (ghcb, Tracked(ghcb_perm)) =
            boxed_ptr!(GuestHostCommunicationBlock, &DEKO_FRAME_ALLOCATOR_FULL);
        let (stack_ptr, _) = boxed_ptr!([u8; 0x8000], &DEKO_FRAME_ALLOCATOR_FULL);

        kinfo!("Allocated VMSA at", vmsa.page, ", GHCB at", ghcb, ", stack at", stack_ptr);
        let ghcb_gpa = virt_to_phys_checked(
            private_bit,
            shared_bit,
            ghcb.into_vaddr(),
            Tracked(pgtable_perm),
        ).expect("GHCB physical address must be valid");

        let (tss_stack, _) = boxed_ptr!([u8; 0x1000], &DEKO_FRAME_ALLOCATOR_FULL);
        let mut tss = X86Tss {
            reserved0: 0,
            stacks: Array::new([tss_stack.addr() as u64, 0, 0]),
            _reserved1: 0,
            ist_stacks: Array::fill(0),
            _reserved2: 0,
            _reserved3: 0,
            io_bmp_base: 0,
        };
        let (tss_ptr, Tracked(mut tss_perm)) = boxed_ptr!(X86Tss, &DEKO_FRAME_ALLOCATOR_FULL);
        tss_ptr.write(Tracked(&mut tss_perm), tss);

        let (gdt_ptr, Tracked(gdt_perm)) =
            boxed_ptr!(GlobalDescriptorTable, &DEKO_FRAME_ALLOCATOR_FULL);
        let gdt = GlobalDescriptorTable::new_vmpl1(
            tss_ptr.addr() as _,
            core::mem::size_of::<X86Tss>() as u32,
        );
        gdt_ptr.write(Tracked(&mut gdt_perm), gdt);

        proof_with!(=> Tracked(db_perm));
        let (db_ptr, db_pa) = HVDoorbell::allocate(true);

        let doorbell = DekoRwLock::new(
            DekoAtomicData::new_with(db_ptr, Tracked(db_perm)),
            IrqUnSafeLockGuard {  },
            Ghost(HvDoorbellPtrPred {  }),
        );

        proof {
            use_type_invariant(&doorbell);
        }

        let (nested_irq, Tracked(nested_irq_perm)) = IrqState::new();

        proof_with!(|= Tracked(
            DekoCpuCtxPerVmplPermission {
                vmsa_perm,
                ghcb_perm,
                nested_irq_perm,
            }
        ));
        Self {
            vmpl,
            vmsa,
            ghcb,
            ghcb_gpa,
            doorbell,
            doorbell_pa: db_pa,
            vmpl1_stack: VirtAddr(stack_ptr.into_vaddr().0.wrapping_add(0x8000)),
            tss: tss_ptr,
            gdt: gdt_ptr,
            current_pid: None,
            slot_dirty: false,
            pending_export_pid: None,
            pending_export_target_cpu: None,
            pending_export_version: 0,
            last_export_ack_version: 0,
            nested_irq,
            deferred_timer_event: false,
            syscall_switch_in_progress: false,
            last_timer_notify_tsc: 0,
        }
    }

    /// Initialize the per-VMPL extended context for this CPU core.
    #[verus_spec(
        with
            Tracked(perm): Tracked<&mut DekoCpuCtxPerVmplPermission>,
            Tracked(pgtable_perm): Tracked<&PageTablePermission>,
        requires
            pgtable_perm.wf(),
            self.wf(),
            self.wf_with(*old(perm)),
            private_bit == pgtable_perm.private_bit,
            shared_bit == pgtable_perm.shared_bit,
        ensures
            self.wf_with(*perm),
    )]
    pub fn init(
        &self,
        cpu_id: u64,
        css: u64,
        tss: &X86Tss,
        private_bit: u64,
        shared_bit: u64,
        cr3: u64,
    ) {
        let init_ctx = VmsaInitialContext::new_with(setup_vmpl1_func_ptr(), css, cr3, tss);

        proof_with!(Tracked(&mut perm.vmsa_perm));
        let sev_features = self.vmsa.init_from(&init_ctx, self.vmpl);

        let (ghcb, Tracked(ghcb_perm), ghcb_gpa) = current_ghcb();

        let vmsa_paddr = virt_to_phys(
            private_bit,
            shared_bit,
            self.vmsa.vaddr(),
            Tracked(pgtable_perm),
        );

        // Register the VMSA for this VMPL.
        GuestHostCommunicationBlock::register_vmsa(
            ghcb,
            Tracked(ghcb_perm),
            vmsa_paddr,
            cpu_id,
            self.vmpl as _,
            sev_features,
            0,
            ghcb_gpa,
        );
    }
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
    pub ghcb: DekoPPtr<GuestHostCommunicationBlock>,
    /// The gpa of the ghcb.
    pub ghcb_gpa: PhysAddr,
    pub tss: X86Tss,
    /// The page table of this CPU.
    pub pgtable: DekoPPtr<PageTable>,
    /// The stack for doing context switches.
    pub ctx_switch_stack: Option<VirtAddr>,
    /// The stack for handling interrupts.
    pub ist_stack: Option<DekoIstStack>,
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
    /// Guest APIC interface for this CPU.
    pub guest_apic: Option<DekoSafeRwLock<X86LocalApic, (), X86LocalApicPred>>,
    /// Runqueue
    pub run_queue: Option<DekoSafeRwLock<DekoRunQueue, DekoRunQueuePermission, DekoRunQueuePred>>,
    /// Temporary mapping for creating temporary mappings to a 4k physical page.
    pub temp_mapping_4k: VirtualMemoryTemporary,
    /// Temporary mapping for creating temporary mappings to a 2M physical page.
    ///
    /// Note that for efficiency this mapping is not frequently used; unless, for
    /// example, a guest explicitly requests us to perform some validations on a
    /// 2M page (pvalidate, for example).
    pub temp_mapping_2m: VirtualMemoryTemporary,
    /// The VMSA for VMPL0 [fixed and will not change].
    pub deko_vmsa: DekoOnceCell<VmsaPage, VmsaPagePermission, VmsaPagePred>,
    /// The doorbell for SEV-SNP restricted interrupt mode.
    ///
    /// The lock only protects the pointer itself from other vCPUs.
    pub doorbell: Option<
        DekoUnsafeRwLock<DekoPPtr<HVDoorbell>, HvDoorbellPtrPermission, HvDoorbellPtrPred>,
    >,
    /// How many disable requests are nested.
    #[deko(skip)]
    pub nested_irq: IrqState,
    /// Current active stack. This is mostly used for stack unwinder.
    pub current_stack: VaddrRange,
    /// The VMPL1 extended context for this CPU, if any.
    /// This is only used when we are running a VMPL1 guest
    pub ext_vmpl1: Option<DekoCpuCtxPerVmpl>,
}

with_permission! {
    DekoCpuCtx,
    ptr_perm: DekoPointsTo<DekoCpuCtx>,
    pgtable_perm: PageTablePermission,
    ghcb_perm: DekoPointsTo<GuestHostCommunicationBlock>,
    vm_region_perm: Option<VirtualMemoryRegionPermission>,
    irq_state_perm: IrqStatePermission,
    ext_vmpl1_perm: Option<DekoCpuCtxPerVmplPermission>,
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
        &&& self.ptr_perm.value().ext_vmpl1 matches Some(ext) ==> self.ext_vmpl1_perm matches Some(
            perm,
        ) && ext.wf_with(perm)
        &&& self.wf()
    }
}

impl WellFormed for DekoCpuCtxPermission {
    open spec fn wf(&self) -> bool {
        &&& self.ptr_perm.is_init()
        &&& self.ptr_perm.wf()
        &&& self.ptr_perm.value().kernel_mapping().wf()
        &&& self.ptr_perm.value().vm_region matches Some(vm) ==> vm.wf()
        &&& self.ptr_perm.value().run_queue matches Some(rq) ==> rq.wf()
        &&& self.ptr_perm.value().doorbell matches Some(db) ==> db.wf()
        &&& self.ptr_perm.value().guest_apic matches Some(ga) ==> ga.wf()
        &&& self.ptr_perm.value().ext_vmpl1 matches Some(ext) ==> ext.wf()
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
        &&& self.irq_state_perm.wf_with(&self.ptr_perm.value().nested_irq)
        &&& self.ptr_perm.value().guest_apic.wf()
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
    // #[deko(skip)]
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
    pub func: Array<CpuidFn, 64>,
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
            r@ =~= Seq::new(64, |i| CpuidFn::empty()),
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
            r@ =~= Seq::new(64 as nat, |i| CpuidFn::empty()),
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
        &&& self.temp_mapping_4k.wf()
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
        &self.temp_mapping_4k
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
        &DekoSafeRwLock<DekoRunQueue, DekoRunQueuePermission, DekoRunQueuePred>,
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
    pub fn temp_mapping_4k(&self) -> (r: &VirtualMemoryTemporary)
        requires
            self.wf(),
        ensures
            r == self.temp_mapping_spec(),
        opens_invariants none
        no_unwind
    {
        &self.temp_mapping_4k
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
        if !is_vmpl1_user() {
            // SAFETY: The PerCPU area is always mapped at the same virtual address, so
            // dereferencing a pointer to that address is safe. The PerCPU area is also
            // never freed, so using a static lifetime is safe as well.
            let (ptr, Tracked(ptr_perm)) = unsafe { DekoPPtr::<Self>::from_raw_uninit(PERCPU_BASE.0)
            };

            (ptr, Tracked::assume_new())
        } else {
            let id = vmpl1_cpuid();
            let addr = PERCPU_BASE_VMPL1.0 + (id as u64 * PAGE_SIZE_2M);
            let (ptr, Tracked(ptr_perm)) = unsafe { DekoPPtr::<Self>::from_raw_uninit(addr) };

            (ptr, Tracked::assume_new())
        }
    }

    pub fn new(
        pgtable: DekoPPtr<PageTable>,
        ghcb: DekoPPtr<GuestHostCommunicationBlock>,
        ghcb_gpa: PhysAddr,
        cpu_id: u64,
        shared_bit: u64,
        private_bit: u64,
        kernel_mapping: MappingSpace,
        vm_region: Option<VirtualMemoryRegion>,
        ctx_switch_stack: Option<VirtAddr>,
        ist_stack: Option<DekoIstStack>,
        run_queue: Option<DekoSafeRwLock<DekoRunQueue, DekoRunQueuePermission, DekoRunQueuePred>>,
        guest_apic: Option<DekoSafeRwLock<X86LocalApic, (), X86LocalApicPred>>,
        irq_state: IrqState,
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
            ghcb_gpa,
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
            temp_mapping_4k: VirtualMemoryTemporary::new_zeroed(),
            temp_mapping_2m: VirtualMemoryTemporary::new_zeroed(),
            deko_vmsa: DekoOnceCell::new(Ghost(VmsaPagePred {  })),
            doorbell: None,
            guest_apic,
            nested_irq: irq_state,
            current_stack: VirtAddr::new(0)..VirtAddr::new(0),  // set to none.
            ext_vmpl1: None,
        }
    }

    #[verifier::external_body]
    fn as_ptr(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.addr(),
            PTE_BASE@ + ((r & 0x0000_FFFF_FFFF_F000u64) >> 9) <= 0x0000_FFFF_FFFF_FFFFu64,
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

    /// Tries to update the mapping of the guest VMSA on this CPU.
    #[verifier::spinoff_prover]
    pub fn update_guest_vmsa(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoCpuCtxPermission>,
    ) -> (r: (bool, Tracked<DekoCpuCtxPermission>))
        requires
            perm.wf_with(ptr),
        ensures
            r.1@.wf_with(ptr),
            r.1@.ptr_perm.value().doorbell == perm.ptr_perm.value().doorbell,
    {
        broadcast use PteFlags::lemma_each_bit_is_valid;

        proof {
            bit_u64_and_auto();
            bit_u32_and_auto();
        }

        let tracked mut perm = perm;

        let cpu_borrow = ptr.borrow(Tracked(&perm.ptr_perm));
        kpanic_if!(
            core::hint::unlikely(cpu_borrow.vm_region.is_none()),
            "Cannot update guest VMSA without VM region"
        );

        let cpu_idx = cpu_borrow.cpu_id as usize;
        deko_rwlock_read_atomic_data!(
            PERCPU_AREAS,
            percpu_areas,
            percpu_areas_perm,
            {
                crate::check_shared_cpu_idx!(cpu_idx, percpu_areas, percpu_areas);

                let guest_vmsa = &get_unchecked(&percpu_areas.0, cpu_idx).guest_vmsa;
                deko_rwlock_write_atomic_data! {
                    guest_vmsa,
                    guest_vmsa,
                    guest_vmsa_perm,
                    {
                        // If generation has changed, we need to update the VMSA mapping.
                        // since the guest/hypervisor may have changed the VMSA physical address.
                        if guest_vmsa.generation == guest_vmsa.gen_in_use {
                            if guest_vmsa.vmsa.is_none() {
                                (false, Tracked(perm))
                            } else {
                                (true, Tracked(perm))
                            }
                        } else {
                            let mut ok = true;
                            // Now we unmap both VMSA and CAA.
                            let DekoCpuCtx {
                                    magic,
                                    cpu_id,
                                    ghcb,
                                    ghcb_gpa,
                                    tss,
                                    pgtable,
                                    ctx_switch_stack,
                                    ist_stack,
                                    private_bit,
                                    shared_bit,
                                    kernel_mapping,
                                    vm_region,
                                    apic,
                                    run_queue,
                                    temp_mapping_4k,
                                    temp_mapping_2m,
                                    deko_vmsa,
                                    doorbell,
                                    nested_irq,
                                    guest_apic,
                                    current_stack,
                                    ext_vmpl1,
                                } = ptr.take(Tracked(&mut perm.ptr_perm));

                                let tracked DekoCpuCtxPermission {
                                    mut ptr_perm,
                                    pgtable_perm,
                                    ghcb_perm,
                                    vm_region_perm,
                                    irq_state_perm,
                                    ext_vmpl1_perm,
                                } = perm;

                                let mut vm_region = vm_region.unwrap();
                                let tracked mut vm_region_perm = vm_region_perm.tracked_unwrap();

                                // Whether or not there are existing mappings, we remove them
                                // and re-insert the new ones.
                                //
                                // Missing mappings are fine as we are going to insert new ones anyway.
                                #[verus_spec(with Tracked(&mut vm_region_perm) => _)]
                                let _ = vm_region.remove(PERCPU_VMSA_BASE);
                                #[verus_spec(with Tracked(&mut vm_region_perm) => _)]
                                let _ = vm_region.remove(PERCPU_CAA_BASE);

                                if let Some(vmsa_paddr) = guest_vmsa.vmsa {
                                    assume(vmsa_paddr@ % PAGE_SIZE as u64 == 0);
                                    assume(vmsa_paddr@ + PAGE_SIZE as u64 <= 0x1_0000_0000_0000);
                                    let vmsa_mapping = make_mapping(VmMapping::PhysMem {
                                        paddr: vmsa_paddr,
                                        size: PAGE_SIZE as _,
                                    });

                                    proof_decl! {
                                        let tracked mut vmsa_mapping_perm;
                                    }

                                    let vmsa_mapping =
                                    #[verus_spec(with Ghost(&vm_region) => Tracked(vmsa_mapping_perm))]
                                    VirtualMemory::new(create_vaddr_range(PERCPU_VMSA_BASE, 1), vmsa_mapping, PteFlags::nx_kernel(), "vmsa_mapping");

                                    kpanic_if!(
                                        core::hint::unlikely(vm_region.areas.len() >= u64::MAX as usize - 2),
                                    );
                                    assume(vm_region.compatible_spec(&vmsa_mapping) && vm_region.disjoint_blocks(&vmsa_mapping));

                                    #[verus_spec(with Tracked(&mut vm_region_perm), Tracked(vmsa_mapping_perm))]
                                    vm_region.insert_at_vaddr(PERCPU_VMSA_BASE, vmsa_mapping);

                                    guest_vmsa.gen_in_use = guest_vmsa.generation;
                                } else {
                                    ok = false;
                                }

                                if let Some(caa_paddr) = guest_vmsa.caa {
                                    assume(caa_paddr@ % PAGE_SIZE as u64 == 0);
                                    assume(caa_paddr@ + PAGE_SIZE as u64 <= 0x1_0000_0000_0000);
                                    let caa_mapping = make_mapping(VmMapping::PhysMem {
                                        paddr: caa_paddr,
                                        size: PAGE_SIZE as _,
                                    });

                                    proof_decl! {
                                        let tracked mut caa_mapping_perm;
                                    }

                                    let caa_mapping =
                                    #[verus_spec(with Ghost(&vm_region) => Tracked(caa_mapping_perm))]
                                    VirtualMemory::new(create_vaddr_range(PERCPU_CAA_BASE, 1), caa_mapping, PteFlags::nx_kernel(), "caa_mapping");

                                    kpanic_if!(
                                        core::hint::unlikely(vm_region.areas.len() >= u64::MAX as usize - 2),
                                    );
                                    assume(vm_region.compatible_spec(&caa_mapping) && vm_region.disjoint_blocks(&caa_mapping));

                                    #[verus_spec(with Tracked(&mut vm_region_perm), Tracked(caa_mapping_perm))]
                                    vm_region.insert_at_vaddr(PERCPU_CAA_BASE, caa_mapping);
                                }

                                proof {
                                    perm = DekoCpuCtxPermission {
                                        ptr_perm,
                                        pgtable_perm,
                                        ghcb_perm,
                                        vm_region_perm: Some(vm_region_perm),
                                        irq_state_perm,
                                        ext_vmpl1_perm,
                                    };
                                }

                                ptr.write(Tracked(&mut perm.ptr_perm), DekoCpuCtx {
                                    magic,
                                    cpu_id,
                                    ghcb,
                                    ghcb_gpa,
                                    tss,
                                    pgtable,
                                    ctx_switch_stack,
                                    ist_stack,
                                    private_bit,
                                    shared_bit,
                                    kernel_mapping,
                                    vm_region: Some(vm_region),
                                    apic,
                                    run_queue,
                                    temp_mapping_4k,
                                    temp_mapping_2m,
                                    deko_vmsa,
                                    doorbell,
                                    nested_irq,
                                    current_stack,
                                    guest_apic,
                                    ext_vmpl1,
                                });

                                (ok, Tracked(perm))
                            }
                    }
                }
            }
        )
    }

    /// Sets up the VMPL1 extended context for this CPU. This should only be called once when we are
    /// initializing the VMPL1 guest. After this function is called, the VMPL1 extended context will be
    /// set up and the VMSA for VMPL1 will be registered to GHCB.
    #[verus_spec]
    pub fn setup_vmpl1(ptr: DekoPPtr<Self>, Tracked(perm): Tracked<&mut DekoCpuCtxPermission>)
        requires
            old(perm).wf_with(ptr),
            old(perm).ptr_perm.value().ctx_switch_stack is Some,
        ensures
            perm.wf_with(ptr),
            perm.ptr_perm.value().ext_vmpl1 is Some,
            perm.ext_vmpl1_perm is Some,
    {
        let cr3 = read_cr3();  // re-use it.
        let mut cpu = ptr.take(Tracked(&mut perm.ptr_perm));
        let cpu_id = cpu.cpu_id;
        let private_bit = cpu.private_bit;
        let shared_bit = cpu.shared_bit;

        proof_with!(Tracked(&mut perm.pgtable_perm) => Tracked(mut ext_vmpl1_perm));
        let ext_vmpl1 = DekoCpuCtxPerVmpl::new(VMPL_GUEST_SECURE_APP as _, private_bit, shared_bit);
        proof_with!(Tracked(&mut ext_vmpl1_perm), Tracked(&perm.pgtable_perm));
        ext_vmpl1.init(
            cpu_id,
            cpu.ctx_switch_stack.unwrap().0,
            &cpu.tss,
            private_bit,
            shared_bit,
            cr3,
        );

        cpu.ext_vmpl1 = Some(ext_vmpl1);
        proof {
            perm.ext_vmpl1_perm = Some(ext_vmpl1_perm);
        }

        ptr.write(Tracked(&mut perm.ptr_perm), cpu);
        validate_ghcb(ptr, Tracked(perm), true);
    }

    pub fn allocate_guest_vmsa(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut DekoCpuCtxPermission>,
    )
        requires
            old(perm).wf_with(ptr),
        ensures
            perm.wf_with(ptr),
    {
        broadcast use crate::snp::RmpFlags::lemma_each_bit_is_valid;

        proof {
            bit_u64_and_auto();
            bit_u32_and_auto();
        }

        let cpu_borrow = ptr.borrow(Tracked(&perm.ptr_perm));
        let private_bit = cpu_borrow.private_bit;
        let shared_bit = cpu_borrow.shared_bit;
        let cpu_idx = cpu_borrow.cpu_id as usize;

        #[verus_spec(with Tracked(&mut perm.pgtable_perm) => Tracked(mut vmsa_perm))]
        let vmsa = VmsaPage::alloc(RmpFlags::vmpl2()  /* guest vmpl */ );

        #[verus_spec(with Tracked(&mut vmsa_perm))]
        let sev_features = vmsa.init_guest_vmsa(0xffff_fff0);
        // Now we need to register this guest VMSA and notify the GHCB.
        let vaddr = vmsa.vaddr();
        let Some(paddr) = virt_to_phys_checked(
            private_bit,
            shared_bit,
            vaddr,
            Tracked(&perm.pgtable_perm),
        ) else {
            kerror!("Failed to get physical address for guest VMSA allocation");
            die("Guest VMSA physical address translation failed");
        };

        // Update the reference to our newly allocated one.
        deko_rwlock_read_atomic_data!(
            PERCPU_AREAS,
            percpu_areas,
            percpu_areas_perm,
            {
                let Some(ref percpu_areas) = percpu_areas else {
                    die("Per-CPU areas not initialized");
                };

                kpanic_if!(
                    core::hint::unlikely(
                        cpu_idx >= percpu_areas.0.len(),
                    ),
                    "CPU index out of bounds"
                );

                deko_rwlock_write_atomic_data! {
                    get_unchecked(&percpu_areas.0, cpu_idx).guest_vmsa,
                    guest_vmsa,
                    guest_vmsa_perm,
                    {
                        guest_vmsa.vmsa.replace(paddr);
                    }
                };
            }
        );
    }

    /// Allocates a VMSA for the given entry point for AP launches.
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
        // Explanation:
        //
        // The `rmpadjust` refuses to modify the RMP entry is the current VMPL <= target
        // VMPL even if we are VMPL0. So it is impossible to modify a page into VMSA page
        // if we use VMPL0. However though, the VMSA page itself is *ignorant* of the
        // the rwx bits so we can just use arbitrary flags as long as they are valid.
        // Using VMPL/2/3 is fine.

        let flags = RmpFlags::vmpl1();
        proof {
            bit_u32_and_auto();
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

        let paddr = PhysAddr(paddr.0.wrapping_add(vmsa.idx as u64 * PAGE_SIZE));

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

        kinfo!("Populating the VMSA from initial context");

        #[verus_spec(with Tracked(&mut vmsa_perm))]
        let sev_features = vmsa.init_from(&init_ctx, VMPL_GUEST_DEKO_MONITOR as _);
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

    pub open spec fn ghcb_spec(&self) -> DekoPPtr<GuestHostCommunicationBlock> {
        self.ghcb
    }

    // When possible, define all these getter and setter by macros.
    #[verifier::when_used_as_spec(ghcb_spec)]
    #[inline]
    pub fn ghcb(&self) -> (r: DekoPPtr<GuestHostCommunicationBlock>)
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
    pub fn setup_cpu<A: DekoFrameAllocator>(
        init_pgtable: DekoPPtr<PageTable>,
        private_bit: u64,
        shared_bit: u64,
        kernel_mapping: MappingSpace,
        id: u64,
        allocator: &A,
    ) -> DekoPPtr<DekoCpuCtx> {
        broadcast use PteFlags::lemma_each_bit_is_valid;
        broadcast use PteFlags::lemma_from_bits_single;
        broadcast use VirtAddr::lemma_page_size_eq_shifts;
        broadcast use VirtAddr::lemma_page_shift_le_max;
        broadcast use VirtAddr::lemma_pfn_roundtrip;
        // We first allocate a new CPU context

        let (cpu_ctx_ptr, Tracked(ctx_perm)) = DekoPageFrameBox::<DekoCpuCtx>::new_zeroed_in(
            allocator,
        );
        let (ghcb, Tracked(ghch_perm)) = boxed_ptr!(GuestHostCommunicationBlock, allocator);
        let ghcb_gpa = virt_to_phys(
            private_bit,
            shared_bit,
            ghcb.into_vaddr(),
            Tracked(&pgtable_perm),
        );

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
            false,
        );

        // Create a mapping for the CPU area itself.
        let mapping = {
            let mapping = VmMapping::PhysMem { paddr, size: PAGE_SIZE };

            proof {
                assume(mapping.wf());
            }

            let arc = DekoUnsafeRwLock::new(
                DekoAtomicData::new_with(mapping, Tracked(())),
                IrqUnSafeLockGuard,
                Ghost(VmMappingPred {  }),
            );

            proof {
                use_type_invariant(&arc);
            }

            DekoArc::new(
                DekoAtomicData::new(arc),
                &DEKO_FRAME_ALLOCATOR_FULL,
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
            "vm_block_for_self",
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
            let mut stack = DekoKernelStack::new_with_size(STACK_SIZE, false);
            stack.alloc_pages(private_bit, shared_bit, &DEKO_FRAME_ALLOCATOR_FULL);
            let top_of_the_stack = VirtAddr(stack.stack_top() + CONTEXT_SWITCH_STACK.0);
            let stack = VmMapping::Stack { stack };

            proof {
                assert(stack.mapping_size_spec() >= PAGE_SIZE) by {
                    assert(0x8000u64 >> 12 == 8) by (bit_vector);
                }
            }
            let arc = DekoUnsafeRwLock::new(
                DekoAtomicData::new_with(stack, Tracked(())),
                IrqUnSafeLockGuard,
                Ghost(VmMappingPred {  }),
            );

            proof {
                use_type_invariant(&arc);
            }

            (
                DekoArc::new(
                    DekoAtomicData::new(arc),
                    &DEKO_FRAME_ALLOCATOR_FULL,
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
            VirtAddr(top_of_the_css_stack.0 - STACK_SIZE)..top_of_the_css_stack,
            cpu_css_stack,
            PteFlags::nx_kernel(),
            "context_switch_stack",
        );

        proof {
            assume(vm_block_for_stack.wf());
            // The same proofs.
            assume(vm_region.compatible_spec(&vm_block_for_stack));
            assume(vm_region.disjoint_blocks(&vm_block_for_stack));
        }

        proof_with!(Tracked(&mut vm_perm), Tracked(vm_block_for_stack_perm));
        vm_region.insert_at_vaddr(
            VirtAddr(top_of_the_css_stack.0 - STACK_SIZE),
            vm_block_for_stack,
        );

        // Allocate a stack for interrupt service routines.
        let (ist_df_stack, top_of_ist_stack) = {
            let stack = DekoKernelStack::new_with_size(STACK_SIZE, false);
            let top_of_the_stack = VirtAddr(stack.stack_top() + STACK_IST_DF_BASE.0);
            let stack = VmMapping::Stack { stack };

            proof {
                assert(stack.mapping_size_spec() >= PAGE_SIZE) by {
                    assert(0x8000u64 >> 12 == 8) by (bit_vector);
                }
            }

            let arc = DekoUnsafeRwLock::new(
                DekoAtomicData::new_with(stack, Tracked(())),
                IrqUnSafeLockGuard {  },
                Ghost(VmMappingPred {  }),
            );

            proof {
                use_type_invariant(&arc);
            }

            (
                DekoArc::new(
                    DekoAtomicData::new(arc),
                    &DEKO_FRAME_ALLOCATOR_FULL,
                    Ghost(DekoSimpleRwLockPred {  }),
                ),
                top_of_the_stack,
            )
        };

        proof_with!(Ghost(&vm_region) => Tracked(vm_block_for_ist_stack_perm));
        let vm_block_for_ist_stack = VirtualMemory::new(
            VirtAddr(top_of_ist_stack.0 - STACK_SIZE)..top_of_ist_stack,
            ist_df_stack,
            PteFlags::nx_kernel(),
            "ist_df_stack",
        );
        proof {
            assume(vm_block_for_ist_stack.wf());
            // The same proofs.
            assume(vm_region.compatible_spec(&vm_block_for_ist_stack));
            assume(vm_region.disjoint_blocks(&vm_block_for_ist_stack));
        }

        proof_with!(Tracked(&mut vm_perm), Tracked(vm_block_for_ist_stack_perm));
        vm_region.insert_at_vaddr(
            VirtAddr(top_of_ist_stack.0 - STACK_SIZE),
            vm_block_for_ist_stack,
        );

        // let cpu_ist_stack = DekoIstStack { df_stack: Some(cpu_ist_stack), df_ss: None };
        let (run_queue, Tracked(run_queue_perm)) = DekoRunQueue::new();
        let run_queue = DekoRwLock::new(
            DekoAtomicData::new_with(run_queue, Tracked(run_queue_perm)),
            IrqSafeLockGuard {  },
            Ghost(DekoRunQueuePred {  }),
        );
        let (irq_state, Tracked(irq_state_perm)) = IrqState::new();

        let guest_apic = DekoSafeRwLock::new(
            DekoAtomicData::new(X86LocalApic::new()),
            IrqSafeLockGuard {  },
            Ghost(X86LocalApicPred {  }),
        );

        let mut cpu_ctx = DekoCpuCtx::new(
            init_pgtable,
            ghcb,
            ghcb_gpa,
            id,
            shared_bit,
            private_bit,
            kernel_mapping,
            Some(vm_region),
            Some(top_of_the_css_stack),
            None,
            Some(run_queue),
            Some(guest_apic),
            irq_state,
        );

        cpu_ctx.temp_mapping_4k.set(
            PERCPU_TEMP_BASE_4K,
            ((PERCPU_TEMP_END_4K.0 - PERCPU_TEMP_BASE_4K.0) / PAGE_SIZE) as usize,
        );
        cpu_ctx.temp_mapping_2m.set(
            PERCPU_TEMP_BASE_2M,
            ((PERCPU_TEMP_END_2M.0 - PERCPU_TEMP_BASE_2M.0) / PAGE_SIZE_2M) as usize,
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

    /// Start the kernel task on this CPU.
    ///
    /// This function takes an option "schedule_now" which indicates whether
    /// the task should be scheduled immediately or not. If true, the task
    /// will be added to the runqueue and scheduled right away. If false,
    /// the task will be added to the runqueue but up to the caller to determine
    /// if the task should be scheduled.
    ///
    /// If "schedule_now", then we will call [`task::schedule`] to switch
    /// the current context to the new task.
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut DekoCpuCtxPermission>,
        requires
            old(perm).wf_with(ptr),
            old(perm).ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
            old(perm).ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf(),
            task.wf(),
        ensures
            perm.wf_with(ptr),
            perm.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
            perm.ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf(),
    )]
    pub fn set_idle_task(ptr: DekoPPtr<Self>, task: DekoRunnablePtr) {
        // Now insert into the runqueue.
        let cpu_ctx = ptr.borrow(Tracked(&perm.ptr_perm));

        kpanic_if!(core::hint::unlikely(
            cpu_ctx.run_queue.is_none()),
            "Runqueue is not initialized for CPU",
            cpu_ctx.cpu_id,
        );

        let lock = cpu_ctx.run_queue.as_ref().unwrap();
        proof {
            use_type_invariant(&lock);
        }
        let mut write_handle = lock.acquire_write();
        let DekoAtomicData { data: mut runqueue, mut perm } = write_handle.get();

        kpanic_if!(core::hint::unlikely(runqueue.run_list.len() >= usize::MAX - 1),
            "Runqueue is full for CPU",
            cpu_ctx.cpu_id,
        );

        proof_with!(Tracked(perm.borrow_mut()));
        runqueue.set_idle_task(task);

        write_handle.release_write(DekoAtomicData::new_with(runqueue, perm));
    }

    pub fn start_kernel_task(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut DekoCpuCtxPermission>,
        task: DekoRunnablePtr,
    )
        requires
            old(perm).wf_with(ptr),
            old(perm).ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
            old(perm).ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf(),
            task.wf(),
        ensures
            perm.wf_with(ptr),
            perm.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
            perm.ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf(),
            perm.ptr_perm.value().cpu_id == old(perm).ptr_perm.value().cpu_id,
            perm.ptr_perm.value().ctx_switch_stack == old(perm).ptr_perm.value().ctx_switch_stack,
    {
        let cpu = ptr.borrow(Tracked(&perm.ptr_perm));

        kpanic_if!(core::hint::unlikely(
            cpu.run_queue.is_none()),
            "Runqueue is not initialized for CPU",
            cpu.cpu_id,
        );

        let lock = cpu.run_queue.as_ref().unwrap();
        deko_rwlock_write_atomic_data! {
            lock,
            runqueue,
            rq_perm,
            {
                #[verus_spec(with Tracked(rq_perm.borrow_mut()))]
                runqueue.handle_task(task.clone());
            }
        }

        deko_rwlock_write_atomic_data! {
            DEKO_TASK_LIST,
            runqueue,
            rq_perm,
            {
                kpanic_if!(
                    core::hint::unlikely(runqueue.run_list.len() >= usize::MAX),
                    "Runqueue is full for CPU",
                    cpu.cpu_id,
                );

                #[verus_spec(with Tracked(rq_perm.borrow_mut()))]
                runqueue.push_back(task);
            }
        }

        // Now perform a scheduling.
        task::schedule();
    }

    pub fn cleanup_terminated_task(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<&DekoCpuCtxPermission>,
    )
        requires
            perm.wf_with(ptr),
            perm.ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf(),
    {
        let cpu = ptr.borrow(Tracked(&perm.ptr_perm));
        let rq = cpu.run_queue.as_ref().unwrap();

        deko_rwlock_write_atomic_data! {
            rq,
            runqueue,
            rq_perm,
            {
                #[verus_spec(with Tracked(rq_perm.borrow_mut()))]
                runqueue.cleanup_terminated_task();
            }
        }
    }

    pub fn schedule_prep(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut DekoCpuCtxPermission>,
    ) -> (r: Option<(DekoRunnablePtr, DekoRunnablePtr)>)
        requires
            old(perm).wf_with(ptr),
            old(perm).ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf(),
        ensures
            r matches Some((cur, next)) ==> {
                &&& cur.wf()
                &&& next.wf()
            },
            perm.wf_with(ptr),
            perm.ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf(),
    {
        let mut cpu = ptr.take(Tracked(&mut perm.ptr_perm));
        let rq = cpu.run_queue.as_ref().unwrap();

        let r =
            deko_rwlock_write_atomic_data! {
            rq,
            runqueue,
            rq_perm,
            {
                match runqueue.current {
                    Some(_) => {
                        #[verus_spec(with Tracked(rq_perm.borrow_mut()))]
                        runqueue.schedule_prep()
                    },
                    None => None,
                }
            }
        };

        if let Some((_, ref next)) = r {
            cpu.current_stack = next.as_ref().data.stack.clone();
        }
        ptr.write(Tracked(&mut perm.ptr_perm), cpu);

        r
    }

    /// Emulate APIC accesses from the guest.
    ///
    /// Since the hypervisor cannot directly inject interrupts or IPI to the guest,
    /// we need to emulate the APIC accesses from the guest and update the interrupt
    /// state accordingly on the calling area page.
    #[verus_spec(
        with
            Tracked(perm): Tracked<&DekoCpuCtxPermission>,
        requires
            perm.wf_with(ptr),
    )]
    pub fn emulate_apic_guest(ptr: DekoPPtr<Self>) {
        proof_with!(Tracked(perm) => Tracked(vmsa_perm));
        let vmsa = VMSA::this_vmsa(ptr);

        proof_with!(Tracked(perm) => Tracked(caa_perm));
        let caa = CaaArea::this_caa(ptr);
        let cpu_borrow = ptr.borrow(Tracked(&perm.ptr_perm));

        kpanic_if!(
            core::hint::unlikely(
                cpu_borrow.guest_apic.is_none()),
            "Guest APIC not initialized for CPU",
            cpu_borrow.cpu_id,
        );

        deko_rwlock_write_atomic_data! {
            cpu_borrow.guest_apic.as_ref().unwrap(),
            apic,
            __,
            {
                #[verus_spec(with Tracked(&mut caa_perm), Tracked(&mut vmsa_perm))]
                apic.serve_guest(cpu_borrow.cpu_id as usize, caa, vmsa);
            }
        }
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
    pub fn setup_idle_task(ptr: DekoPPtr<Self>, entry: u64, name: &'static str) {
        let cpu_id = ptr.borrow(Tracked(&perm.ptr_perm)).cpu_id;

        // Create a new idle task.
        proof_with!(Tracked(perm) => Tracked(mut new_perm));
        let task = DekoRunnable::new(
            ptr,
            DekoTaskArgs {
                parent: None,
                entry,
                name,
                mode: task::DekoTaskMode::Kernel {
                    entry,
                    param: cpu_id,
                    ret: crate::cpu::task::run_kernel_tasks_func_ptr(),
                },
            },
        );

        kinfo!("Created idle task for CPU ", cpu_id);

        proof_with!(Tracked(&mut new_perm));
        DekoCpuCtx::set_idle_task(ptr, task);  // idle task should not be scheduled immediately.

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
    kinfo!("Setting up CPU context for AP: ", which.apic_id);

    proof_with!(Tracked(pgtable_perm) => Tracked(mut cpu_perm));
    let cpu_ctx = DekoCpuCtx::setup_cpu(
        init_pgtable,
        bsp.private_bit,
        bsp.shared_bit,
        bsp.kernel_mapping.clone(),
        which.apic_id as u64,
        &DEKO_FRAME_ALLOCATOR_FULL,
    );

    kinfo!("Allocating VMSA for AP: ", which.apic_id);
    let (vmsa, sev_features) = DekoCpuCtx::allocate_deko_vmsa(
        cpu_ctx,
        Tracked(&mut cpu_perm),
        cpu_entry,
    );

    kinfo!("VMSA allocated at physical address: ", vmsa => hex);

    // Now invoke the ap creation routine.
    let (ghcb, Tracked(ghcb_perm), ghcb_gpa) = current_ghcb();
    kdebug!("ap_create arguments:");
    kdebug!("  ghcb: ", ghcb);
    kdebug!("  apic_id: ", which.apic_id);
    kdebug!("  vmsa: ", vmsa);
    kdebug!("  sev_features: ", sev_features);

    kinfo!("Invoking AP creation for AP: ", which.apic_id);
    GuestHostCommunicationBlock::ap_create(
        ghcb,
        Tracked(ghcb_perm),
        which.apic_id,
        sev_features,
        0,
        vmsa,
        ghcb_gpa,
    );
}

/// Other APs will start execution from here.
#[allow(improper_ctypes_definitions)]
#[no_mangle]
#[verus_spec()]
#[verifier::exec_allows_no_decreases_clause]
unsafe extern "C" fn ap_start() -> ! {
    // BSP must have initialized DekoCpuCtx and map the per-cpu area onto the AP's
    // own page table.
    let (cpu_ctx_ptr, Tracked(mut ap_perm)) = DekoCpuCtx::this_cpu();
    let cpuid = cpu_ctx_ptr.borrow(Tracked(&ap_perm.ptr_perm)).cpu_id;

    // Now we must initialize the GHCB on this cpu.
    kpanic_if!(cpuid == 0, "AP started with CPU ID 0, which is reserved for BSP");

    msr_register_ghcb_gpa(validate_ghcb(cpu_ctx_ptr, Tracked(&mut ap_perm), false));

    kinfo!("AP CPU", cpuid => hex, "is starting.");
    let is_vm_region_none = cpu_ctx_ptr.borrow(Tracked(&ap_perm.ptr_perm)).vm_region.is_none();
    if core::hint::unlikely(is_vm_region_none) {
        die("AP CPU VM region is not initialized");
    }
    let is_run_queue_none = cpu_ctx_ptr.borrow(Tracked(&ap_perm.ptr_perm)).run_queue.is_none();
    if core::hint::unlikely(is_run_queue_none) {
        die("AP CPU run queue is not initialized");
    }
    assume(ap_perm.ptr_perm.value().vm_region_spec().unwrap().wf());
    assume(ap_perm.ptr_perm.value().run_queue_spec().unwrap().wf());
    // Also setup the APIC for this cpu.
    crate::imp::setup_apic(cpu_ctx_ptr, Tracked(&mut ap_perm));

    // Also set the idle task.
    proof_with!(Tracked(ap_perm));
    DekoCpuCtx::setup_idle_task(cpu_ctx_ptr, cpu_idle_func_ptr(), "cpu_idle");

    sse_init();

    add_ipi_available_cpu();

    deko_rwlock_write_atomic_data! {
        PERCPU_AREAS,
        percpu_areas,
        percpu_areas_perm,
        {
            crate::check_shared_cpu_idx!(cpuid as usize, percpu_areas, percpu_areas);

            let this = &percpu_areas.0[cpuid as usize];

            let tracked mut this_perm = percpu_areas_perm.borrow_mut().shared_perms.tracked_remove(cpuid as int);
            let ghost old = this_perm;
            loop
                invariant
                    this_perm.online_perm.is_for(this.online),
                    this_perm.ipi_irr_perm == old.ipi_irr_perm,
                    this_perm.ipi_pending_perm == old.ipi_pending_perm,
                    this_perm.nmi_pending_perm == old.nmi_pending_perm,
                    this_perm.ipi_shared_perm == old.ipi_shared_perm,
            {
                core::hint::spin_loop();

                match this.online.compare_exchange_weak(Tracked(&mut this_perm.online_perm), false, true) {
                    Ok(old) if old => {
                        die("AP CPU is already marked online in per-CPU shared area");
                    },
                    Ok(_) => break ,
                    Err(_) => continue ,
                }
            }

            proof {
                percpu_areas_perm.borrow_mut().shared_perms.tracked_insert(cpuid as int, this_perm);
            }
        }
    }

    kinfo!("Application processor started;", cpuid => hex, "entering idle loop.");

    schedule_init();

    // wait for schedule.
    loop {
    }
}

func_ptr!(ap_start);

#[inline(always)]
#[verifier::external_body]
pub fn rdrand64_step() -> [u8; 8] {
    let mut val: u64;
    let mut success = 0u8;

    loop {
        unsafe {
            core::arch::asm!(
                "rdrand {0}",
                "setc {1}",
                out(reg) val,
                out(reg_byte) success,
                options(nomem, nostack),
            );
        }

        if success == 1 {
            return val.to_le_bytes();
        }
    }
}

} // verus!
#[macro_export]
macro_rules! check_shared_cpu_idx {
    ($idx:expr, $against:ident, $binding:ident) => {
        let Some(ref $binding) = $against else {
            $crate::die("Per-CPU areas not initialized");
        };

        $crate::kpanic_if!(
            core::hint::unlikely($idx >= $binding.0.len(),),
            "CPU index out of bounds",
            $idx,
            "but max is",
            $binding.0.len(),
        );
    };
}
