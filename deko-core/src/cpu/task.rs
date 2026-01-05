use core::cmp::Ordering;
use core::ops::{Add, Range};
use core::sync::atomic::{AtomicU32, AtomicU64};

use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::address::{MappingSpace, VaddrRange, VirtAddr};
use deko_std::array::Array;
use deko_std::bits::bit_u64_and_auto;
use deko_std::cpu::{CpuID, X86GeneralRegs};
use deko_std::list::{LinkedList, Node};
use deko_std::mem::bitalloc::{DekoBitAlloc, DekoBitmapAllocator1024};
use deko_std::mem::{
    DekoFrameAllocator, PAGE_SIZE, PERTASK_BASE, PGTABLE_LVL3_IDX_SHARED, STACK_SIZE,
};
use deko_std::misc::early_dbg;
use deko_std::prelude::{func_ptr, VADDR_UPPER_MASK};
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::sync::arc::DekoArc;
use deko_std::sync::rwlock::{DekoRwLock, RwLockPredicate};
use deko_std::sync::{DekoAtomicData, DekoSimpleRwLock, DekoSimpleRwLockPred, RwLock};
use deko_std::wf::WellFormed;
use deko_std::{
    boxed_ptr, deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data, with_permission,
    TrivialPredicate,
};
use vstd::prelude::*;
use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl, PartialOrdSpecImpl};

use crate::collections::Vec;
use crate::cpu::ipi::{wait_ipi_blocking, DekoIpIMessage, DekoIpiRequest};
use crate::cpu::irq::{irq_enable, no_irq_zone, DekoUnsafeRwLock, IrqUnSafeLockGuard};
use crate::cpu::regs::{sse_restore_context, sse_save_context};
use crate::cpu::{
    self, flush_tlb_global_percpu, flush_tlb_global_sync, DekoCpuCtx, DekoCpuCtxPermission,
    CPUID_MAX_COUNT, CPU_NUM, PERCPU_AREAS,
};
use crate::guest::{handle_guest_exit, DekoGuestExitInformation, DekoGuestServError};
use crate::imp::doorbell::HVDoorbell;
use crate::imp::ghcb::{vmpl_switch, GuestHostCommunicationBlock};
use crate::imp::vmsa::VMSA;
use crate::mm::frame_allocator::DekoPageFrameAllocator;
use crate::mm::paging::{
    bit_not_in_addr_region, bit_not_overlapping, PageTable, PageTablePermission, PteFlags,
};
use crate::mm::stack::DekoKernelStack;
use crate::mm::vm::{
    self, VirtualMemory, VirtualMemoryPermission, VirtualMemoryRegion,
    VirtualMemoryRegionPermission, VirtualMemoryRegionPred, VmMapping, VmMappingPred, VMR_GRANULE,
};
use crate::mm::{virt_to_phys, DEKO_FRAME_ALLOCATOR, DEKO_FRAME_ALLOCATOR_FULL};
use crate::{dbg, die, kdebug, kerror, kinfo, kpanic_if, kunimplemented, kwarn};

core::arch::global_asm!(
    include_str!("switch.S"),
    TASK_RSP_OFFSET = const core::mem::offset_of!(DekoRunnable, rsp),
    options(att_syntax)
);

const _: () = {
    assert!(core::mem::offset_of!(X86ExceptionContext, frame.flags) == 0x98);
};

verus! {

pub const DEKO_DEFAULT_STACK_SIZE: u64 = 0x10000;

pub exec static DEKO_KTASK_BIT_ALLOC: DekoSimpleRwLock<DekoBitmapAllocator1024, IrqUnSafeLockGuard>
    ensures
        DEKO_KTASK_BIT_ALLOC.wf(),
{
    let allocator = DekoBitmapAllocator1024::new_empty();
    let r = DekoSimpleRwLock::new_simple(allocator, IrqUnSafeLockGuard {  });

    proof {
        use_type_invariant(&r);
    }

    r
}

#[verifier::external_body]
#[inline]
pub const fn deko_rsp_offset() -> u64 {
    core::mem::offset_of!(DekoRunnable, rsp) as u64
}

/// Ask the bit allocator to give us a VM region index for a new task.
#[verifier::external_body]
#[verus_spec(r =>
    ensures
        r matches Some((idx, region)) ==> {
            &&& 0 <= idx < DekoBitmapAllocator1024::cap_spec()
            &&& region.start@ % VMR_GRANULE == 0
            &&& region.end@ % VMR_GRANULE == 0
            &&& region.start@ >= VADDR_UPPER_MASK
            &&& region.wf()
        }
)]
pub fn request_vm_region() -> Option<(usize, VaddrRange)> {
    let r =
        deko_rwlock_write_atomic_data!(
        DEKO_KTASK_BIT_ALLOC,
        alloc,
        __,
        {
            alloc.alloc(1, 0)
        }
    );

    match r {
        None => None,
        Some(idx) => {
            let span = 0x8000000000u64 / DekoBitmapAllocator1024::cap() as u64;
            let base = PERTASK_BASE.0 + (idx * span as usize) as u64;

            Some((idx, VirtAddr(base)..VirtAddr(span as u64 + base)))
        },
    }
}

/// The interrupt frame saved during an x86 interrupt.
#[repr(C)]
#[derive(DekoDebug, Clone, Copy)]
pub struct X86InterruptFrame {
    pub rip: u64,
    pub cs: u64,
    pub flags: u64,
    pub rsp: u64,
    pub ss: u64,
}

/// The context saved during an x86 exception.
#[repr(C)]
#[derive(DekoDebug, Clone, Copy)]
pub struct X86ExceptionContext {
    pub ssp: usize,
    pub regs: X86GeneralRegs,
    pub error_code: usize,
    pub frame: X86InterruptFrame,
}

/// The memory management information of a task.
pub struct DekoTaskMM {
    /// The page table index covered by the MM for quick
    /// lookups. This index ensures that the top-level
    /// page table entry is always reserved for the task MM.
    pub pgtable_index: usize,
    /// The virtual memory region of the task for kernel level.
    pub k_vm_region: VirtualMemoryRegion,
    /// The virtual memory region of the task for user level.
    pub u_vm_region: Option<VirtualMemoryRegion>,
}

with_permission! {
    DekoTaskMM,
    // pgtable_perm: Tracked<PageTablePermission>, will it own the permission?
    k_vm_region_perm: Tracked<VirtualMemoryRegionPermission>,
    u_vm_region_perm: Tracked<Option<VirtualMemoryRegionPermission>>,
}

with_atomic_pred! {
    DekoTaskMM,
    DekoTaskMMPermission,
    fields: { k_vm_region, u_vm_region, },
    perm_fields: { k_vm_region_perm, u_vm_region_perm, },
    k_vm_region.wf_with(&k_vm_region_perm.view())
        && match (&u_vm_region, u_vm_region_perm.view()) {
            (Some(vm), Some(vm_perm)) => vm.wf_with(&vm_perm),
            (None, None) => true,
            _ => false,
        }
}

fn on_task_exit() {
    kinfo!("Task exited");

    schedule();
}

#[verus_verify]
impl DekoTaskMM {
    #[verus_spec(r =>
        with
            Tracked(u_vm_region_perm): Tracked<Option<VirtualMemoryRegionPermission>>,
        requires
            match (&u_vm_region, &u_vm_region_perm) {
                (Some(vm), Some(vm_perm)) => vm.wf_with(&vm_perm),
                (None, None) => true,
                _ => false,
            },
    )]
    pub fn new(u_vm_region: Option<VirtualMemoryRegion>) -> Self {
        // TODO: We may also need a global bitmap allocator so that
        // some pages can be reserved for specific purposes only.
        kunimplemented!()
    }
}

pub broadcast axiom fn xsave_area_size_wf()
    ensures
        #[trigger] Array::<u8, 4096>::size_wf(),
;

/// Generates a unique identifier for a task.
///
/// Note that we reserve the value `0` and `1` for special purposes,
/// so the generated IDs will always be greater than or equal to `2`.
#[verifier::external_body]
#[verus_spec(r =>
    ensures
        2 <= r <= u64::MAX,
)]
pub(crate) fn generate_id() -> u64 {
    static ID_COUNTER: AtomicU64 = AtomicU64::new(2);

    let mut id = ID_COUNTER.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
    while id < 2 {
        id = ID_COUNTER.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
    }

    id
}

/// The predicate for the global run queue that:
///
/// - Ensures the run queue is well-formed.
/// - Ensures its associated permission type is well-formed with respect to the run queue.
with_atomic_pred! {
    DekoRunQueue,
    DekoRunQueuePermission,
    fields: { },
    perm_fields: { },
    data.wf() && data.wf_with(perm)
}

pub exec static DEKO_TASK_LIST: DekoUnsafeRwLock<
    DekoRunQueue,
    DekoRunQueuePermission,
    DekoRunQueuePred,
> = {
    let (queue, Tracked(queue_perm)) = DekoRunQueue::new();

    DekoRwLock::new(
        DekoAtomicData { data: queue, perm: Tracked(queue_perm) },
        IrqUnSafeLockGuard {  },
        Ghost(DekoRunQueuePred {  }),
    )
};

#[repr(u64)]
#[derive(DekoDebug, Clone, Copy)]
pub enum DekoRunnableState {
    RUNNING = 0,
    BLOCKED = 1,
    TERMINATED = 2,
}

#[repr(C)]
#[derive(DekoDebug, Clone, Copy)]
pub struct DekoRunnableSchedState {
    /// Whether this is an idle task
    pub idle_task: bool,
    /// Current state of the task
    pub state: DekoRunnableState,
    /// CPU this task is currently assigned to
    pub cpu_index: usize,
}

impl WellFormed for DekoRunnableSchedState {
    open spec fn wf(&self) -> bool {
        &&& self.cpu_index < CPUID_MAX_COUNT as usize
        &&& self.idle_task ==> !(self.state matches DekoRunnableState::TERMINATED)
    }
}

with_atomic_pred!(
    DekoRunnableSchedState,
    (),
    fields: {  },
    perm_fields: {  },
    data.wf()
);

// impl RwLockPredicate<DekoAtomicData<DekoRunQueue, DekoRunQueuePermission>> for DekoRunqueuePred {
//     #[verifier::inline]
//     open spec fn inv(self, data: DekoAtomicData<DekoRunQueue, DekoRunQueuePermission>) -> bool {
//         &&& data.data.wf()
//         &&& data.data.wf_with(data.perm@)
//     }
// }
/// The arguments passed to a task upon its creation to specify
/// its initial configuration.
#[derive(DekoDebug)]
pub struct DekoTaskArgs {
    /// If this task is spawned by another task, this field holds
    /// a pointer to the parent task.
    pub parent: Option<DekoRunnablePtr>,
    /// The entry point of the new task which should be the pointer
    /// to the function to execute.
    #[deko(hex)]
    pub entry: u64,
    /// The name of the task for debugging purposes.
    #[deko(hex)]
    pub name: &'static str,
    /// The mode in which the task should run.
    pub mode: DekoTaskMode,
}

impl WellFormed for DekoTaskArgs {
    open spec fn wf(&self) -> bool {
        &&& self.parent matches Some(parent) ==> parent.wf()
    }
}

/// The mode in which a task is running.
#[derive(DekoDebug)]
pub enum DekoTaskMode {
    /// User mode task.
    User { entry: u64 },
    /// Kernel mode task.
    Kernel { entry: u64, param: u64, ret: u64 },
}

impl WellFormed for DekoTaskMode {
    open spec fn wf(&self) -> bool {
        true
    }
}

/// A task run queue that manages the scheduling of runnable tasks.
///
/// The [`DekoRunQueue`] maintains a collection of tasks that are ready to execute
/// and tracks the currently running task. It serves as the core data structure
/// for the task scheduler, enabling preemptive multitasking by organizing tasks
/// in a priority-based execution order.
///
/// # Usage
///
/// The run queue is typically used by the kernel's task scheduler to:
/// - Add new runnable tasks to the execution queue
/// - Select the next task to run based on scheduling policies
/// - Track the currently executing task for context switching
#[derive(DekoDebug)]
pub struct DekoRunQueue {
    /// The list of runnable tasks queued for execution.
    #[deko(skip)]
    pub run_list: LinkedList<DekoRunnablePtr>,
    /// The currently running task.
    pub current: Option<DekoRunnablePtr>,
    /// The idle task pointer.
    pub idle: Option<DekoRunnablePtr>,
    /// The terminated task pointer.
    pub terminated: Option<DekoRunnablePtr>,
    /// Someone put the task here so the current CPU
    /// must take care with it.
    pub wake: Option<DekoRunnablePtr>,
    /// CPU Affinity.
    pub affinity: Option<DekoCpuAffinity>,
}

impl View for DekoRunQueue {
    type V = Seq<DekoAtomicData<DekoRunnable, DekoRunnablePermission>>;

    /// The view on the [`DekoRunQueue`] is the sequence of runnable tasks
    /// in the run list (n.B: deep view of the [`DekoArc<T>`] not its PTR addr).
    open spec fn view(&self) -> Self::V {
        Seq::new(self.run_list@.len() as nat, |i: int| { self.run_list@[i as int]@ })
    }
}

with_permission!(
    DekoRunQueue,
    run_list_perm: Ghost<Seq<Ghost<DekoRunnablePtr>>>,
    current_ptr: Option<DekoRunnablePtr>,
    idle_ptr: Option<DekoRunnablePtr>,
    terminated_ptr: Option<DekoRunnablePtr>,
    wake_ptr: Option<DekoRunnablePtr>,
);

impl WellFormed for DekoRunQueue {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.run_list.wf()
        &&& self.current.wf()
        &&& self.current matches Some((task_ptr)) ==> {
            &&& task_ptr.wf()
        }
        &&& self.idle.wf()
        &&& self.terminated.wf()
        &&& self.wake.wf()
        &&& self.affinity matches Some((task_ptr, cpu_index)) ==> {
            &&& task_ptr.wf()
            &&& cpu_index < CPUID_MAX_COUNT as u64
        }
        &&& forall|i: int|
            #![trigger self.run_list@[i as int]]
            0 <= i < self.run_list@.len() ==> {
                let task_ptr = self.run_list@[i as int];

                task_ptr.wf()
            }
    }
}

#[verus_verify]
impl DekoCpuCtx {
    #[verus_spec(
        with
            Tracked(perm): Tracked<&DekoCpuCtxPermission>,
        requires
            perm.wf_with(ptr),
    )]
    pub fn runqueue_info(ptr: DekoPPtr<Self>) {
        let rq = &ptr.borrow(Tracked(&perm.ptr_perm)).run_queue;
        let id = ptr.borrow(Tracked(&perm.ptr_perm)).cpu_id;

        if let Some(rq) = rq {
            deko_rwlock_read_atomic_data! {
                rq,
                runqueue,
                runqueue_perm,
                {
                    #[verus_spec(with Tracked(runqueue_perm.borrow()))]
                    runqueue.info();
                }
            }
        }
    }
}

#[verus_verify]
impl DekoRunQueue {
    pub open spec fn wf_with(&self, perm: DekoRunQueuePermission) -> bool {
        &&& self.wf()
        &&& perm.run_list_perm@.len() == self.run_list@.len()
        &&& perm.idle_ptr.wf()
        &&& perm.current_ptr.wf()
        &&& perm.terminated_ptr.wf()
        &&& perm.wake_ptr.wf()
        // &&& perm.current_ptr is Some <==> self.current is Some
        // &&& perm.idle_ptr is Some <==> self.idle is Some
        // &&& perm.terminated_ptr is Some <==> self.terminated is Some
        // &&& perm.wake_ptr is Some <==> self.wake is Some
        // &&& perm.current_ptr matches Some(current_ptr) ==> {
        //     &&& self.current matches Some(current) ==> current@@ == current_ptr@@
        // }
        // &&& perm.idle_ptr matches Some(idle_ptr) ==> {
        //     &&& self.idle matches Some(idle) ==> idle@@ == idle_ptr@@
        // }
        // &&& perm.terminated_ptr matches Some(terminated_ptr) ==> {
        //     &&& self.terminated matches Some(terminated) ==> terminated@@ == terminated_ptr@@
        // }
        // &&& perm.wake_ptr matches Some(wake_ptr) ==> {
        //     &&& self.wake matches Some(wake) ==> wake@@ == wake_ptr@@
        // }
        &&& forall|i: int|
            #![trigger self.run_list@[i as int], perm.run_list_perm@[i as int]]
            0 <= i < perm.run_list_perm@.len() ==> self.run_list@[i as int]@
                == perm.run_list_perm@[i as int]@@
    }

    /// Checks if the run queue has any scheduleable tasks.
    ///
    /// If there is no running task then we schedule the idle one.
    /// To make the system functional there must be at least one
    /// task in the run queue or an idle task or nobody can wake
    /// up the system and thus making it useless.
    pub open spec fn is_scheduleable_spec(&self) -> bool {
        &&& self.run_list@.len() > 0 || self.idle matches Some(_)
    }

    /// Checks if the run queue has any scheduleable tasks.
    #[inline]
    #[verifier::when_used_as_spec(is_scheduleable_spec)]
    #[verus_spec(r =>
        requires
            self.wf(),
        ensures
            r == self.is_scheduleable_spec(),
    )]
    pub fn is_scheduleable(&self) -> bool {
        self.run_list.len() > 0 || self.idle.is_some()
    }

    /// Prints debugging information about the run queue.
    #[verus_spec(
        with
            Tracked(perm): Tracked<&DekoRunQueuePermission>,
        requires
            self.wf(),
            self.wf_with(*perm),
    )]
    pub fn info(&self) {
        kinfo!("Runqueue info:");
        if let Some(current) = &self.current {
            kinfo!("  Current task: ", current.as_ref().data);
        } else {
            kinfo!("  Current task: None");
        }
        if let Some(idle) = &self.idle {
            kinfo!("  Idle task: ", idle.as_ref().data);
        } else {
            kinfo!("  Idle task: None");
        }
        if let Some(terminated) = &self.terminated {
            kinfo!("  Terminated task: ", terminated.as_ref().data);
        } else {
            kinfo!("  Terminated task: None");
        }
        if let Some(wake) = &self.wake {
            kinfo!("  Wake task: ", wake.as_ref().data);
        } else {
            kinfo!("  Wake task: None");
        }

        if let Some(head) = self.run_list.head.as_ref() {
            let mut ptr = head;
            let len = self.run_list.len();
            kinfo!("  Runlist length: ", len);

            for i in 0..len
                invariant
                    0 <= i <= self.run_list@.len(),
                    self.run_list.wf(),
                    len == self.run_list@.len() == self.run_list.inner@.ptrs.len(),
                    i < self.run_list@.len() ==> {
                        &&& ptr == self.run_list.inner@.ptrs[i as int]
                        &&& self.run_list.node_wf_at(i as nat)
                    },
                    self.run_list.head.is_some(),
            {
                let v = ptr.borrow(
                    Tracked(self.run_list.inner.borrow().perms.tracked_borrow(i as nat)),
                );

                kinfo!("  Runlist[", i, "]: ", v.value.as_ref().data);

                if i + 1 < len {
                    ptr = v.next.as_ref().unwrap();
                }
            }
        }
    }

    #[verus_spec(r =>
        with
            -> node_perm: Tracked<DekoPointsTo<Node<DekoRunnablePtr>>>,
        requires
            task.wf(),
        ensures
            node_perm@.pptr() == r@,
            node_perm@.wf(),
            node_perm@.is_init(),
            node_perm@.value()@ == task,
    )]
    fn make_node(task: DekoRunnablePtr) -> DekoPPtr<Node<DekoRunnablePtr>> {
        let (node_ptr, Tracked(mut node_perm)) =
            boxed_ptr!(Node<DekoRunnablePtr>, &DEKO_FRAME_ALLOCATOR_FULL);
        // write to the node.
        node_ptr.write(
            Tracked(&mut node_perm),
            Node { prev: None, next: None, value: task.clone() },
        );

        proof_with!(|= Tracked(node_perm));
        node_ptr
    }

    #[verus_spec(
        with
            Tracked(perm): Tracked<&mut DekoRunQueuePermission>,
        requires
            old(self).wf(),
            old(self).run_list@.len() < usize::MAX,
            old(self).wf_with(*old(perm)),
            task.wf(),
        ensures
            self.wf(),
            self@ =~= old(self)@.insert(old(self)@.len() as int, task@),
            self.wf_with(*perm),
    )]
    pub fn push_back(&mut self, task: DekoRunnablePtr) {
        proof_with!(=> Tracked(node_perm));
        let node_ptr = Self::make_node(task.clone());

        self.run_list.push_back_no_alloc(node_ptr, Tracked(node_perm));
        proof {
            perm.run_list_perm@ = perm.run_list_perm@.insert(
                perm.run_list_perm@.len() as int,
                Ghost(task),
            );
        }
    }

    #[verus_spec(
        with
            Tracked(perm): Tracked<&mut DekoRunQueuePermission>,
        requires
            old(self).wf(),
            old(self).run_list@.len() < usize::MAX,
            old(self).wf_with(*old(perm)),
            task.wf(),
        ensures
            self.wf(),
            self@ =~= old(self)@.insert(0, task@),
            self.wf_with(*perm),
    )]
    pub fn push_front(&mut self, task: DekoRunnablePtr) {
        proof_with!(=> Tracked(node_perm));
        let node_ptr = Self::make_node(task.clone());

        self.run_list.push_front_no_alloc(node_ptr, Tracked(node_perm));

        proof {
            perm.run_list_perm@ = perm.run_list_perm@.insert(0, Ghost(task));
        }
    }

    /// Update state before a task is scheduled out. Non-idle tasks in RUNNING
    /// state will be put at the end of the run_list. Terminated tasks will be
    /// stored in the terminated_task field of the run queue and be destroyed
    /// after the task-switch.
    #[verus_spec(
        with
            Tracked(perm): Tracked<&mut DekoRunQueuePermission>,
        requires
            old(self).wf(),
            old(self).wf_with(*old(perm)),
            task.wf(),
        ensures
            self.wf(),
            self.wf_with(*perm),
    )]
    pub fn handle_task(&mut self, task: DekoRunnablePtr) {
        let DekoAtomicData { data: task_ref, .. } = task.as_ref();

        if task_ref.is_running() && !task_ref.is_idle() {
            kpanic_if!(
                core::hint::unlikely(self.run_list.len() >= usize::MAX),
                "Run queue is full when scheduling out a running task"
            );  // make verus happy.

            proof_with!(Tracked(perm));
            self.push_back(task);
        } else if task_ref.is_terminated() {
            self.terminated.replace(task.clone());
            proof {
                perm.terminated_ptr = Some(task);
            }
        }
    }

    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut DekoRunQueuePermission>,
        requires
            old(self).wf(),
            old(self).wf_with(*old(perm)),
            old(self).current is Some,
        ensures
            self.wf_with(*perm),
            self.current is Some,
            r matches Some((cur, next)) ==> {
                &&& cur.wf()
                &&& next.wf()
            }
    )]
    pub fn schedule_prep(&mut self) -> Option<(DekoRunnablePtr, DekoRunnablePtr)> {
        let current = self.current.take().unwrap();

        proof_with!(Tracked(perm));
        self.handle_task(current.clone());

        proof_with!(Tracked(perm));
        let next = self.get_next_task();
        self.current = Some(next.clone());

        if current == next {
            None
        } else {
            Some((current, next))
        }
    }

    #[inline]
    #[verus_spec(
        with
            Tracked(perm): Tracked<&mut DekoRunQueuePermission>,
        requires
            old(self).wf(),
            old(self).wf_with(*old(perm)),
        ensures
            self.wf(),
            self.wf_with(*perm),
    )]
    pub fn cleanup_terminated_task(&mut self) {
        if let Some(terminated_task) = self.terminated.take() {
            // Drop the task here.
            terminated_task.free();

            proof {
                perm.terminated_ptr = None;
            }
        }
    }

    /// Try to get the next task to run. This function panics if there
    /// both the run list is empty and there is no idle task.
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut DekoRunQueuePermission>,
        requires
            old(self).wf(),
            old(self).wf_with(*old(perm)),
        ensures
            self.wf(),
            self.wf_with(*perm),
            r.wf(),
    )]
    pub fn get_next_task(&mut self) -> DekoRunnablePtr {
        if self.run_list.len() == 0 {
            match &self.idle {
                Some(idle_ptr) => { idle_ptr.clone() },
                None => {
                    die("No idle task is found.");
                },
            }
        } else {
            proof {
                assert(self.run_list@.len() > 0);
            }

            let (task, Tracked(mut task_perm)) = self.run_list.pop_front_no_alloc();
            let task = task.take(Tracked(&mut task_perm)).value;

            proof {
                perm.run_list_perm = Ghost(perm.run_list_perm@.remove(0));
            }

            task
        }
    }

    /// Sets the idle task of the run queue; if there was a previous idle task,
    /// the task pointer is returned.
    ///
    /// This also pushes the new idle task to the front of the global run queue.
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut DekoRunQueuePermission>,
        requires
            old(self).wf_with(*old(perm)),
            old(self).run_list@.len() < usize::MAX - 1,
            idle.wf(),
        ensures
            self@ =~= old(self)@,
            self.wf_with(*perm),
            r =~= old(self).idle,
    )]
    pub fn set_idle_task(&mut self, idle: DekoRunnablePtr) -> Option<DekoRunnablePtr> {
        let state_lock = &idle.as_ref().data.state;
        deko_rwlock_write_atomic_data! {
            state_lock,
            state,
            state_perm,
            {
                kpanic_if!(
                    core::hint::unlikely(matches!(state.state, DekoRunnableState::TERMINATED)),
                    "Trying to set an already terminated task as idle task"
                );

                state.idle_task = true;
            }
        }

        let old = self.idle.replace(idle.clone());

        deko_rwlock_write_atomic_data! {
            DEKO_TASK_LIST,
            global_rq,
            global_rq_perm,
            {
                kpanic_if!(
                    core::hint::unlikely(global_rq.run_list.len() >= usize::MAX),
                    "Global run queue is full when setting idle task"
                );

                #[verus_spec(with Tracked(global_rq_perm.borrow_mut()))]
                global_rq.push_front(idle.clone());
            }
        }

        old
    }

    /// Schedules the next task to run from the run queue.
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut DekoRunQueuePermission>,
        requires
            old(self).wf(),
            old(self).wf_with(*old(perm)),
            old(self).is_scheduleable_spec(),
        ensures
            self.wf_with(*perm),
            self.current is Some,
            r.wf(),
    )]
    pub fn schedule_init(&mut self) -> DekoRunnablePtr {
        proof_with!(Tracked(perm));
        let next_task = self.get_next_task();

        self.current = Some(next_task.clone());
        next_task
    }
}

pub struct DekoPagaTablePred;

impl RwLockPredicate<
    DekoAtomicData<DekoPPtr<PageTable>, PageTablePermission>,
> for DekoPagaTablePred {
    #[verifier::inline]
    open spec fn inv(self, data: DekoAtomicData<DekoPPtr<PageTable>, PageTablePermission>) -> bool {
        true
    }
}

/// The context of a runnable task when it is executed.
///
/// This records the necessary registers and CPU states to temporarily
/// store when a task is not running, allowing it to be resumed later.
#[repr(C)]
#[derive(Clone, DekoDebug)]
pub struct DekoRunnableCtx {
    #[deko(hex)]
    pub rsp: u64,
    pub regs: X86GeneralRegs,
    #[deko(hex)]
    pub flags: u64,
    #[deko(hex)]
    pub ret: u64,
}

/// A [`DekoRunnable`] represents a task that can be scheduled by the
/// task scheduler.
///
/// This is OS-level process. Each process will have several sub-processes/threads.
#[derive(DekoDebug)]
pub struct DekoRunnable {
    /// The stack pointer of the task.
    #[deko(hex)]
    pub rsp: u64,
    /// The SSP of the task.
    pub ssp: VirtAddr,
    /// The unique id of the task.
    pub id: u64,
    /// The name of the task for debugging purposes.
    pub name: &'static str,
    /// The priority of the task.
    pub priority: u8,
    /// The page table of the task.
    pub pgtable: DekoUnsafeRwLock<DekoPPtr<PageTable>, PageTablePermission, DekoPagaTablePred>,
    /// The stack owned by the task.
    pub stack: VaddrRange,
    /// The area allocated for XSAVE/XSTOR.
    pub xsave: DekoPPtr<Array<u8, 4096>>,
    /// The size of the XSAVE area.
    #[deko(hex)]
    pub xsave_size: usize,
    /// The memory management.
    pub mm: DekoArc<VirtualMemoryRegion, VirtualMemoryRegionPermission, VirtualMemoryRegionPred>,
    /// The state of this task.
    pub state: DekoUnsafeRwLock<DekoRunnableSchedState, (), DekoRunnableSchedStatePred>,
}

#[verus_verify]
impl DekoRunnable {
    /// Createas and initializes a new virtual memory manager for the task.
    #[verus_spec(r =>
        requires
            ms.wf(),
            bit_not_overlapping(private_bit),
            bit_not_overlapping(shared_bit),
            bit_not_in_addr_region(private_bit),
            bit_not_in_addr_region(shared_bit),
        ensures
            r.wf(),
    )]
    pub fn create_mm(private_bit: u64, shared_bit: u64, ms: MappingSpace) -> DekoArc<
        VirtualMemoryRegion,
        VirtualMemoryRegionPermission,
        VirtualMemoryRegionPred,
    > {
        let (pgtable, _, Tracked(pgtable_perm)) = PageTable::new(
            private_bit,
            shared_bit,
            Ghost(&ms),
        );
        let flags = PteFlags::from_bits_truncate(0);
        proof {
            bit_u64_and_auto();
        }

        let (idx, region) = match request_vm_region() {
            Some((idx, region)) => (idx, region),
            None => {
                kerror!("Failed to allocate VM region for new task");
                die("");
            },
        };

        kdebug!("Allocated VM region for new task: index", idx, "region", region);

        // TODO: Where should the virtual region come from?
        // Perhaps we'll need some allocator to do so.
        proof_with!(Tracked(pgtable_perm), => Tracked(vm_region_perm));
        let vmr = VirtualMemoryRegion::new(
            region.start,
            region.end,
            flags,
            pgtable,
            ms,
            private_bit,
            shared_bit,
        );

        DekoArc::new(
            DekoAtomicData::new_with(vmr, Tracked(vm_region_perm)),
            &DEKO_FRAME_ALLOCATOR_FULL,
            Ghost(VirtualMemoryRegionPred {  }),
        )
    }

    #[verus_spec(r =>
        with
            Tracked(vm_region_perm): Tracked<&mut VirtualMemoryRegionPermission>,
            Tracked(xsave_perm): Tracked<&DekoPointsTo<Array<u8, 4096>>>,
        requires
            old(vm_region).wf_with(old(vm_region_perm)),
            xsave@ == xsave_perm.pptr(),
        ensures
            vm_region.wf(),
            vm_region.wf_with(vm_region_perm),
            old(vm_region_perm).pgtable_perm.private_bit == vm_region_perm.pgtable_perm.private_bit,
            old(vm_region_perm).pgtable_perm.shared_bit == vm_region_perm.pgtable_perm.shared_bit,
            r.1.end >= r.1.start,
            r.0@ + r.1.end < u64::MAX,
    )]
    pub fn alloc_user_stack(
        vm_region: &mut VirtualMemoryRegion,
        entry: u64,
        xsave: DekoPPtr<Array<u8, 4096>>,
    ) -> (VirtAddr, Range<u64>, u64) {
        kunimplemented!()
    }

    #[verifier::external_body]
    #[verus_spec(
        requires
            // TODO: need to ensure that stack.ptr is mapped and valid.
    )]
    pub fn push_stack_frames(stack_ptr: u64, entry: u64, xsave: u64, params: u64, ret: u64) {
        unsafe {
            let task_ctx_ptr = (stack_ptr - core::mem::size_of::<
                DekoRunnableCtx,
            >() as u64) as *mut DekoRunnableCtx;
            (*task_ctx_ptr).regs.rdi = entry;
            (*task_ctx_ptr).regs.rsi = xsave;
            (*task_ctx_ptr).regs.rdx = params;
            (*task_ctx_ptr).ret = ret;
            (*task_ctx_ptr).flags = 0x2;

            (stack_ptr as *mut u64).write(on_task_exit as u64);
        }
    }

    /// This function allocates the kernel stack for a new task.
    ///
    /// It does the following stuff:
    ///
    /// - Allocates the kernel stack pages via the frame allocator.
    /// - Creates the mapping on the current CPU.
    /// - Prepare the context on the stack so that when we switch to
    ///   this task it will start executing from the entry point.
    ///
    /// The return value is a triple of:
    ///
    /// - The stack mapping in the new task's VM region.
    /// - The stack's bound (excluding the guard pages).
    /// - The offset to the task context in the stack.
    #[verus_spec(r =>
        with
            Tracked(vm_region_perm): Tracked<&mut VirtualMemoryRegionPermission>,
            Tracked(pgtable_perm): Tracked<&PageTablePermission>,
            Tracked(xsave_perm): Tracked<&DekoPointsTo<Array<u8, 4096>>>,
        requires
            pgtable_perm.wf(),
            allocator.wf(),
            private_bit == pgtable_perm.private_bit,
            shared_bit == pgtable_perm.shared_bit,
            old(vm_region).wf(),
            old(vm_region).wf_with(old(vm_region_perm)),
            old(vm_region).areas@.len() + 1 < u64::MAX as int,
            xsave@ == xsave_perm.pptr(),
        ensures
            vm_region.wf(),
            vm_region.wf_with(vm_region_perm),
            old(vm_region_perm).pgtable_perm.private_bit == vm_region_perm.pgtable_perm.private_bit,
            old(vm_region_perm).pgtable_perm.shared_bit == vm_region_perm.pgtable_perm.shared_bit,
            r.1.end >= r.1.start,
            r.0@ + r.1.end < u64::MAX,
    )]
    pub fn alloc_kernel_stack<A: DekoFrameAllocator>(
        vm_region: &mut VirtualMemoryRegion,
        private_bit: u64,
        shared_bit: u64,
        allocator: &A,
        entry: u64,
        param: u64,
        ret: u64,
        xsave: DekoPPtr<Array<u8, 4096>>,
    ) -> (VirtAddr, Range<u64>, u64) {
        let mut stack = DekoKernelStack::new_with_size(STACK_SIZE, false);

        proof_with!(Tracked(pgtable_perm));
        stack.alloc_pages(private_bit, shared_bit, allocator);

        let range = stack.range();

        let mapping = {
            let stack = VmMapping::Stack { stack };

            proof {
                assert(stack.mapping_size_spec() >= PAGE_SIZE) by {
                    assert(STACK_SIZE >> 12 == 13) by (bit_vector);
                }
            }

            let mapping_lock = DekoRwLock::new(
                DekoAtomicData::new(stack),
                IrqUnSafeLockGuard {  },
                Ghost(VmMappingPred {  }),
            );

            proof {
                use_type_invariant(&mapping_lock);
            }

            DekoArc::new(
                DekoAtomicData::new(mapping_lock),
                &DEKO_FRAME_ALLOCATOR_FULL,
                Ghost(DekoSimpleRwLockPred {  }),
            )
        };

        proof {
            use_type_invariant(&mapping);
            bit_u64_and_auto();
        }

        // Insert the new stack mapping into the given VM region.
        let vaddr = match #[verus_spec(with Tracked(vm_region_perm))]
        vm_region.insert(mapping.clone(), PteFlags::nx_kernel()) {
            Some(vaddr) => vaddr,
            None => {
                kerror!("Failed to insert kernel stack mapping into VM region");
                die("");
            },
        };

        proof {
            assume(114514 < vaddr@ + range.end < u64::MAX);
        }

        // We need to setup a context on the stack that matches the stack layout
        // defined in switch_context below.
        let stack_tos = vaddr.0 + range.end;
        // Need space for task handler.
        let stack_offset = 8;  // == core::mem::size_of::<u64>();
        let stack_ptr = (stack_tos - stack_offset);

        kdebug!("Allocated kernel stack at virtual address: ", vaddr => hex);
        // 'Push' the task frame onto the stack
        //
        // SAFETY: we ensure that both `TaskContext` and the function pointer
        // can be written to valid memory. The address storing the function
        // pointer is always 8b-aligned.
        // The processor flags must always be in a default state, unrelated
        // to the flags of the caller.  In particular, interrupts must be
        // disabled because the task switch code expects to execute a new
        // task with interrupts disabled.
        Self::push_stack_frames(stack_ptr, entry, xsave.addr() as u64, param, ret);

        (vaddr, range, 0x98  /* stack_offset + ctx_size */ )
    }

    /// Creates a new runnable task with the given arguments on the given CPU.
    #[verus_spec(r =>
        with
            Tracked(ctx_perm): Tracked<DekoCpuCtxPermission>,
            -> ctx_perm_updated: Tracked<DekoCpuCtxPermission>,
        requires
            ctx_perm.wf_with(cpu),
            ctx_perm.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
            ctx_perm.ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf(),
            args.wf(),
        ensures
            r.wf(),
            ctx_perm_updated@.wf_with(cpu),
            ctx_perm_updated@.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
            ctx_perm_updated@.ptr_perm.value().run_queue_spec() matches Some(rq) && rq.wf(),
            ctx_perm_updated@.ptr_perm.value().cpu_id == ctx_perm.ptr_perm.value().cpu_id,
            // r@.???
    )]
    pub fn new(cpu: DekoPPtr<DekoCpuCtx>, args: DekoTaskArgs) -> DekoRunnablePtr {
        let cpu_borrowed = cpu.borrow(Tracked(&ctx_perm.ptr_perm));

        kpanic_if!(core::hint::unlikely(
            cpu_borrowed.vm_region().is_none(),
        ), "CPU has no VM region assigned");

        let private_bit = cpu_borrowed.private_bit;
        let shared_bit = cpu_borrowed.shared_bit;

        // Allocate a page table for the new task.
        let (new_pgtable, _, Tracked(mut pgtable_perm)) = PageTable::new(
            private_bit,
            shared_bit,
            Ghost(&cpu_borrowed.kernel_mapping_spec()),
        );

        // This is a trick to avoid copying all the shared mappings
        // one by one. We just copy the PTE from the kernel page table
        // where the PDPE for shared mappings is stored; thus shared pages
        // will be accessible in the new page table as well.
        let old_pte_value = *cpu_borrowed.pgtable.borrow(
            Tracked(&ctx_perm.pgtable_perm.pgtable_perm),
        ).0.index(PGTABLE_LVL3_IDX_SHARED as usize);

        // Copy the shared mappings from the kernel page table.
        PageTable::update_entry_by_ptr(
            new_pgtable,
            Tracked(&mut pgtable_perm.pgtable_perm),
            PGTABLE_LVL3_IDX_SHARED as usize,
            old_pte_value,
        );

        proof {
            broadcast use xsave_area_size_wf;

            assert(pgtable_perm.wf()) by {
                admit();
            }
        }

        // Allocate xsave areas.
        let (xsave_ptr, Tracked(xsave_perm)) =
            boxed_ptr!(Array<u8, 4096>, &DEKO_FRAME_ALLOCATOR_FULL);
        // This does nothing but clear the area to mark it as init.
        assume(xsave_perm.is_init());

        let tracked mut ctx_perm = ctx_perm;
        let cpu_taken = cpu.take(Tracked(&mut ctx_perm.ptr_perm));
        let DekoCpuCtx {
            magic,
            cpu_id,
            ghcb,
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
        } = cpu_taken;
        kpanic_if!(core::hint::unlikely(
            vm_region.is_none(),
        ), "CPU has no VM region assigned");

        // Allocate a new virtual memory region for the new task.
        let task_mm = match args.parent {
            // If so we inherit the parent's memory management.
            Some(ptr) => { ptr.as_ref().data.mm.clone() },
            // If not just create a new one.
            None => { Self::create_mm(private_bit, shared_bit, kernel_mapping) },
        };

        let tracked DekoCpuCtxPermission {
            ptr_perm,
            pgtable_perm: cpu_pgtable_perm,
            ghcb_perm,
            vm_region_perm,
            irq_state_perm,
        } = ctx_perm;

        let mut vm_region = vm_region.unwrap();
        kpanic_if!(core::hint::unlikely(vm_region.areas.len() as u64 >= u64::MAX - 1 ),
                  "Too many VM areas in the CPU VM region"
        );

        let tracked mut vm_region_perm = vm_region_perm.tracked_unwrap();
        let (stack, vrange, rsp_offset) = match args.mode {
            DekoTaskMode::Kernel { entry, param, ret } => {
                proof_with!(Tracked(&mut vm_region_perm), Tracked(&cpu_pgtable_perm) ,Tracked(&mut xsave_perm));
                Self::alloc_kernel_stack(
                    &mut vm_region,
                    private_bit,
                    shared_bit,
                    &DEKO_FRAME_ALLOCATOR_FULL,
                    entry,
                    param,
                    ret,
                    xsave_ptr,
                )
            },
            DekoTaskMode::User { entry } => {
                proof_with!(Tracked(&mut vm_region_perm), Tracked(&mut xsave_perm));
                Self::alloc_user_stack(&mut vm_region, entry, xsave_ptr)
            },
        };

        proof_with!(Tracked(&mut pgtable_perm), Tracked(&vm_region_perm));
        vm_region.copy_to_page_table(new_pgtable);

        let stack_bounds = VirtAddr(stack.0 + vrange.start)..VirtAddr(stack.0 + vrange.end);

        let task = DekoRunnable {
            id: generate_id(),
            pgtable: RwLock::new(
                DekoAtomicData::new_with(new_pgtable, Tracked(pgtable_perm)),
                IrqUnSafeLockGuard {  },
                Ghost(DekoPagaTablePred {  }),
            ),
            priority: 0,
            xsave: xsave_ptr,
            mm: task_mm,
            rsp: stack_bounds.end.0.checked_sub(rsp_offset).unwrap_or(0),
            ssp: VirtAddr(0),
            stack: stack_bounds,
            xsave_size: PAGE_SIZE as _,
            state: {
                let sched_state = DekoRunnableSchedState {
                    idle_task: false,
                    state: DekoRunnableState::RUNNING,
                    cpu_index: cpu_id as usize,
                };

                DekoRwLock::new(
                    DekoAtomicData::new(sched_state),
                    IrqUnSafeLockGuard {  },
                    Ghost(DekoRunnableSchedStatePred {  }),
                )
            },
            name: args.name,
        };

        proof {
            // need to fix it later.
            assert(task.wf()) by {
                admit();
            }
        }

        let cpu_new = DekoCpuCtx {
            magic,
            cpu_id,
            ghcb,
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
        };
        let tracked ctx_perm = DekoCpuCtxPermission {
            ptr_perm,
            pgtable_perm: cpu_pgtable_perm,
            ghcb_perm,
            vm_region_perm: Some(vm_region_perm),
            irq_state_perm,
        };
        cpu.write(Tracked(&mut ctx_perm.ptr_perm), cpu_new);

        proof_with!(|= Tracked(ctx_perm));
        DekoArc::new(
            DekoAtomicData::new_with(task, Tracked(DekoRunnablePermission { xsave_perm })),
            &DEKO_FRAME_ALLOCATOR_FULL,
            Ghost(DekoRunnablePred {  }),
        )
    }
}

with_permission! {
    DekoRunnable,
    xsave_perm: DekoPointsTo<Array<u8, 4096>>,
}

with_atomic_pred! {
    DekoRunnable,
    DekoRunnablePermission,
    fields: { xsave },
    perm_fields: { xsave_perm },
    xsave_perm.pptr() == xsave@ && xsave_perm.is_init() && xsave_perm.wf()
}

pub type DekoRunnablePtr = DekoArc<DekoRunnable, DekoRunnablePermission, DekoRunnablePred>;

pub type DekoCpuAffinity = (DekoRunnablePtr, u64);

impl WellFormed for DekoRunnable {
    open spec fn wf(&self) -> bool {
        &&& self.rsp % 8 == 0
        &&& self.mm.wf()
        &&& self.stack.wf()
        &&& self.stack.start@ % PAGE_SIZE == 0
        &&& self.stack.end@ % PAGE_SIZE == 0
    }
}

impl PartialEq for DekoRunnable {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl PartialOrd for DekoRunnable {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.priority < other.priority {
            Some(Ordering::Less)
        } else if self.priority > other.priority {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

impl PartialEqSpecImpl for DekoRunnable {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        vstd::std_specs::cmp::PartialEqSpec::eq_spec(&self.id, &other.id)
    }
}

impl PartialOrdSpecImpl for DekoRunnable {
    open spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &Self) -> Option<Ordering> {
        if self.priority < other.priority {
            Some(Ordering::Less)
        } else if self.priority > other.priority {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

#[verus_verify]
impl DekoRunnable {
    #[verus_spec(
        requires
            self.wf(),
    )]
    pub fn set_state(&self, state: DekoRunnableState) {
        let mut handle = self.state.acquire_write();
        let DekoAtomicData { mut data, perm: Tracked(mut perm) } = handle.get();

        let should_end = if matches!(data.state, DekoRunnableState::TERMINATED) {
            kwarn!("Attempt to change state of a terminated task");
            true
        } else if matches!(state, DekoRunnableState::TERMINATED) && data.idle_task {
            kwarn!("Attempt to terminate an idle task");
            true
        } else {
            false
        };

        if should_end {
            handle.release_write(DekoAtomicData::new_with(data, Tracked(perm)));
            return ;
        }
        data.state = state;

        handle.release_write(DekoAtomicData::new_with(data, Tracked(perm)));
    }

    #[verus_spec(
        requires
            self.wf(),
    )]
    pub fn set_idle(&self, idle: bool) {
        let mut handle = self.state.acquire_write();
        let DekoAtomicData { mut data, perm: Tracked(mut perm) } = handle.get();

        let should_end = if idle && matches!(data.state, DekoRunnableState::TERMINATED) {
            kwarn!("Attempt to set a terminated task as idle");
            true
        } else {
            false
        };

        if should_end {
            handle.release_write(DekoAtomicData::new_with(data, Tracked(perm)));
            return ;
        }
        data.idle_task = idle;

        handle.release_write(DekoAtomicData::new_with(data, Tracked(perm)));
    }

    #[verus_spec(r =>
        requires
            self.wf(),
    )]
    pub fn read_state(&self) -> (DekoRunnableState, bool) {
        let (state, idle_task) =
            deko_rwlock_read_atomic_data! {
            self.state,
            state,
            __,
            {
                let idle_task = state.idle_task;
                let state = state.state;

                (state, idle_task)
            }
        };

        (state, idle_task)
    }

    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
    )]
    pub fn is_running(&self) -> bool {
        matches!(self.read_state().0, DekoRunnableState::RUNNING)
    }

    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
    )]
    pub fn is_terminated(&self) -> bool {
        matches!(self.read_state().0, DekoRunnableState::TERMINATED)
    }

    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
    )]
    pub fn is_idle(&self) -> bool {
        self.read_state().1
    }
}

/// Initializes the task scheduler.
///
/// This function will try to switch the current threat into the
/// the idle task and initializes the current task in the run.
///
/// This function is called once and subsequent scheduling is done
/// via [`schedule`].
///
/// # Safety
///
/// Before calling the function, a valid task must be created and
/// properly assigned to the current thread.
#[verus_spec(r =>
        // with ???
    )]
pub unsafe fn schedule_init() {
    // NO IRQ is allowed or the system will jump into
    // an inconsistent state.
    no_irq_zone(
        ||
            {
                let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();
                let cpu = cpu.borrow(Tracked(&perm.ptr_perm));

                match &cpu.run_queue {
                    Some(runqueue) => {
                        let mut handle = runqueue.acquire_write();
                        let DekoAtomicData { data: mut runqueue, perm: Tracked(mut perm) } =
                            handle.get();

                        kpanic_if!(!runqueue.is_scheduleable(),
                                   "No scheduleable task is found.");

                        proof_with!(Tracked(&mut perm));
                        let task = runqueue.schedule_init();

                        handle.release_write(DekoAtomicData::new_with(runqueue, Tracked(perm)));
                        // perform the actual context switch
                        kdebug!("next task to schedule: ", task.as_ref().data);

                        switch(None, task);
                    },
                    None => {
                        die("No active run queue is found.");
                    },
                }
            },
    );
}

/// Schedules the given task to run on the current CPU.
#[verus_spec(
    requires
        task.wf(),
)]
pub fn schedule_this_task(task: DekoRunnablePtr) {
    let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();
    let cpu = cpu.borrow(Tracked(&perm.ptr_perm));
    let rq = cpu.run_queue.as_ref();
    // make verus happy.
    kpanic_if!(core::hint::unlikely(rq.is_none()), "No run queue found when scheduling task");

    // First we set this task as the running.
    deko_rwlock_write_atomic_data! {
        rq.unwrap(),
        runqueue,
        runqueue_perm,
        {
            deko_rwlock_write_atomic_data! {
                &task.as_ref().data.state,
                state,
                __,
                {
                    state.state = DekoRunnableState::RUNNING;
                }
            }

            // Then let it
            #[verus_spec(with Tracked(runqueue_perm.borrow_mut()))]
            runqueue.handle_task(task);
        }
    }

    schedule();
}

/// Schedules the next task to run on the current CPU.
pub fn schedule() {
    let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();
    let cpu_id = cpu.borrow(Tracked(&perm.ptr_perm)).cpu_id;
    let rq = cpu.borrow(Tracked(&perm.ptr_perm)).run_queue.as_ref();
    // make verus happy.
    kpanic_if!(core::hint::unlikely(rq.is_none()), "No run queue found when scheduling task");

    no_irq_zone(
        ||
            {
                let work = DekoCpuCtx::schedule_prep(cpu, Tracked(&perm));
                if let Some((cur, next)) = work {
                    // id generation is somehow incorrect.
                    kinfo!("Switching from task ", cur.as_ref().data.id => hex, " name", cur.as_ref().data.name);
                    kinfo!("Switching to task ", next.as_ref().data.id => hex, " name", next.as_ref().data.name);

                    let next_state = &next.as_ref().data.state;

                    let old_cpu =
                        deko_rwlock_write_atomic_data! {
                        next_state,
                        state,
                        __,
                        {
                            let old = state.cpu_index;

                            old
                        }
                    };

                    // SSE Save context.
                    sse_save_context(cur.as_ref().data.xsave.addr() as u64);

                    switch(Some(cur.clone()), next);

                    // SSE restore context.
                    sse_restore_context(cur.as_ref().data.xsave.addr() as u64);
                }
            },
    );
    after_switch();

    // Remove the terminated task from the task list, if any.
    DekoCpuCtx::cleanup_terminated_task(cpu, Tracked(&perm));
}

/// Attempts to perform the task switch.
///
/// Note that this function must be called with no IRQs enabled.
#[verus_spec(r =>
    requires
        pre.wf(),
        next.wf(),
)]
fn switch(pre: Option<DekoRunnablePtr>, next: DekoRunnablePtr) {
    let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();
    let cpu = cpu.borrow(Tracked(&perm.ptr_perm));
    let Some(stack) = cpu.ctx_switch_stack else {
        die("No context switch stack is assigned to the CPU.");
    };
    let private_bit = cpu.private_bit;
    let shared_bit = cpu.shared_bit;

    let rsp_next = next.as_ref().data.rsp;

    let cr3_next = {
        let read_handle = next.as_ref().data.pgtable.acquire_read();
        let pgtable_vaddr = read_handle.borrow().data.addr() as u64;

        read_handle.release_read();

        // Use this CPU's private and shared bits and page table to translate
        // the virtual address to physical address.
        virt_to_phys(
            private_bit,
            shared_bit,
            VirtAddr::new(pgtable_vaddr),
            Tracked(&perm.pgtable_perm),
        ).0
    };

    let pre = match pre {
        Some(ptr) => DekoArc::as_ptr(&ptr).addr() as u64,
        None => 0,
    };
    let next = DekoArc::as_ptr(&next).addr() as u64;

    // perform the actual context switch
    do_context_switch(pre, next, cr3_next, stack.0);
}

fn after_switch() {
    let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();
    let cpu = cpu.borrow(Tracked(&perm.ptr_perm));
    let Some(rq) = &cpu.run_queue else {
        die("No run queue found after context switch.");
    };

    let affinity =
        deko_rwlock_write_atomic_data! {
        rq,
        runqueue,
        __,
        {
            runqueue.affinity.take()
        }
    };

    if let Some((task, which)) = affinity {
        kdebug!("After switch: setting CPU affinity to core ", which);

        let req = DekoIpiRequest::new(
            &[which as usize],
            DekoIpIMessage::AffinityChange { task: task.clone() },
        );

        req.send_ipi();
    }
}

/// Attempts to perform the task switch.
///
/// # Safety
///
/// The caller must ensure that both `pre` and `next`
/// are valid task pointers (they must be raw so we can
/// use assembly to jump to them).
///
/// Typically this is just an unsafe wrapper for the [`switch`] function
/// that de-reference the [`DekoArc<T>`] to get the raw pointer.
#[verifier::external_body]
fn do_context_switch(pre: u64, next: u64, cr3_next: u64, stack_next: u64) {
    kdebug!("Switching context: pre=", pre => hex);
    kdebug!("Switching context: next=", next => hex);
    kdebug!("Switching context: cr3_next=", cr3_next => hex);
    kdebug!("Switching context: stack_next=", stack_next => hex);

    unsafe {
        core::arch::asm!(
            "call context_switch",
            in("r12") pre,
            in("r13") next,
            in("r14") stack_next,
            in("r15") cr3_next,
            options(att_syntax),
        );
    }
}

} // verus!
verus! {

impl DekoRunQueue {
    /// Creates a new, empty run queue.
    #[inline]
    pub const fn new() -> (r: (Self, Tracked<DekoRunQueuePermission>))
        ensures
            r.0.wf(),
            r.0.wf_with(r.1@),
            !r.0.is_scheduleable(),
    {
        let tracked perm = DekoRunQueuePermission {
            run_list_perm: Ghost(Seq::empty()),
            current_ptr: None,
            idle_ptr: None,
            terminated_ptr: None,
            wake_ptr: None,
        };

        (
            DekoRunQueue {
                run_list: LinkedList::new(),
                current: None,
                idle: None,
                terminated: None,
                wake: None,
                affinity: None,
            },
            Tracked(perm),
        )
    }
}

/// This function's address must be registered on the stack
/// so that `retq` can jump to it; this function does nothing
/// but just some checks.
#[no_mangle]
#[allow(improper_ctypes_definitions)]
#[verifier::exec_allows_no_decreases_clause]
#[verus_spec()]
pub extern "C" fn run_kernel_tasks(
    entry: u64,
    xsave_addr: DekoPPtr<Array<u8, 4096>>,
    start_params: u64,
) {
    kdebug!("Trampoline: entered `run_kernel_tasks:`");
    kdebug!("\tentry = ", entry => hex);
    kdebug!("\txsave_addr = ", xsave_addr.addr() as u64 => hex);
    kdebug!("\tstart_params = ", start_params => hex);

    // Now we need to re-enable the interrupts.
    // Then we enter the entry.
    irq_enable();

    kinfo!("enabled?", cpu::irq::irq_enabled());

    after_switch();

    sse_restore_context(xsave_addr.addr() as u64);

    into(entry, start_params);
}

/// A wrapper function to convert `f` into function pointer type
/// and call it.
#[verifier::external_body]
#[verus_spec()]
#[inline]
fn into(f: u64, args: u64) -> (__: !) {
    let f: fn (u64) = unsafe { core::mem::transmute(f) };

    f(args);

    // This function should NEVER return
    loop {
    }
}

func_ptr!(run_kernel_tasks);

/// Put the current CPU into a busy-wait idle state and set up the
/// runqueue accordingly for next wake up.
pub fn cpu_go_idle(which: usize) {
    let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();
    let cpu = cpu.borrow(Tracked(&perm.ptr_perm));

    kpanic_if!(
        core::hint::unlikely(cpu.run_queue.is_none()),
        "No run queue is assigned to the CPU.",
    );

    kpanic_if!(
        core::hint::unlikely(which != cpu.cpu_id as usize),
        "CPU ID mismatch when going idle.",
    );

    deko_rwlock_write_atomic_data! {
        cpu.run_queue.as_ref().unwrap(),
        rq,
        __,
        {
            kpanic_if!(
                core::hint::unlikely(rq.current.is_none()),
                "No current task is running on the CPU.",
            );

            deko_rwlock_write_atomic_data! {
                rq.current.as_ref().unwrap().as_ref().data.state,
                state,
                __,
                {
                    // set this task as BLOCKED.
                    state.state = DekoRunnableState::BLOCKED;
                }
            }

            kpanic_if!(
                core::hint::unlikely(rq.wake.is_some()),
                "Run queue wake field is already set.",
            );

            // Set the wake field to wake up this task later.
            rq.wake = Some(rq.current.as_ref().unwrap().clone());
        }
    };

    schedule();
}

/// Put the current CPU into idle state and halt it for saving the
/// power unless some other cores wake it up by sending an IPI.
#[verus_spec(r =>
    requires
        which < CPUID_MAX_COUNT,
    ensures
        r.wf(),
)]
#[verifier::exec_allows_no_decreases_clause]
pub fn cpu_idle(which: usize) -> DekoRunnablePtr {
    kinfo!("CPU ", which, " entering idle state.");

    kinfo!("enabled?", cpu::irq::irq_enabled());

    #[verus_spec(
        invariant
            which < CPUID_MAX_COUNT,
    )]
    loop {
        early_dbg();  // <=> hlt, though bad naming

        // Check if there is any IPI sent to this CPU.
        let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();
        let cpu = cpu.borrow(Tracked(&perm.ptr_perm));

        kpanic_if!(
            core::hint::unlikely(cpu.run_queue.is_none()),
            "No run queue is assigned to the CPU.",
        );

        let task =
            deko_rwlock_write_atomic_data! {
            cpu.run_queue.as_ref().unwrap(),
            rq,
            __,
            {
                rq.wake.take()
            }
        };

        if let Some(task) = task {
            // schedule this task.
            kdebug!("Waking up task ", task.as_ref().data.id => hex, "name:", task.as_ref().data.name);
            // Now we need to schedule to this task.
            schedule_this_task(task);
        }
        schedule();
    }
}

func_ptr!(cpu_idle);

/// Sets the CPU affinity for the current task.
///
/// Note this function will block the current task and try to "steal" it
/// from the current CPU to the target CPU to complet the task migration.
///
/// This function is usually called on a service core to migrate the
/// current task to the target core.
#[verus_spec(
    requires
        which < CPUID_MAX_COUNT,
)]
pub fn set_cpu_affinity(which: usize) {
    let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();
    let cpu = cpu.borrow(Tracked(&perm.ptr_perm));

    // Check the runqueue.
    kpanic_if!(
        core::hint::unlikely(cpu.run_queue.is_none()),
        "No run queue is assigned to the CPU.",
    );

    deko_rwlock_write_atomic_data! {
        cpu.run_queue.as_ref().unwrap(),
        rq_data,
        __,
        {
            // Check if we have a current task.
            kpanic_if!(
                core::hint::unlikely(rq_data.current.is_none()),
                "No current task is running on the CPU.",
            );

            // Block the task now.
            let current_task: DekoRunnablePtr = rq_data.current.as_ref().unwrap().clone();

            deko_rwlock_write_atomic_data! {
                current_task.as_ref().data.state,
                state,
                __,
                {
                    state.state = DekoRunnableState::BLOCKED;
                }
            }

            // Then set the affinity of this runqueue.
            rq_data.affinity = Some((current_task.clone(), which as u64));
        }
    }

    schedule();

    // After scheduling, the task should be migrated as we
    // can match `Some` in `after_switch`.
}

/// The main entry point for the kernel service loop.
///
/// This function serves as the divergent execution path for the Boot CPU (BSP)
/// and Application Processors (APs). It is responsible for initializing the
/// scheduling environment for secondary cores and entering the guest execution loop.
///
/// # Behavior
///
/// * **Boot CPU (`cpu_index == 0`):**
///   1. Retrieves the total number of active CPUs from global atomic data.
///   2. Validates that the current CPU has a valid RunQueue and VM Region.
///   3. Iterates through all available APs (indices `1` to `cpu_nums`).
///   4. Creates a new kernel task (`serv_main_ap`) for each AP.
///   5. Schedules these tasks to start the secondary cores.
///
/// * **Application Processors (`cpu_index > 0`):**
///   1. Logs the wake-up event via IPI affinity.
///   2. Sets the CPU affinity to ensure the task is pinned to its respective core.
///
/// Finally, regardless of the core index, the execution flow attempts to enter
/// the guest context via [`try_enter_guest`].
#[verus_spec(
    requires
        cpu_index < CPUID_MAX_COUNT,
)]
#[verifier::spinoff_prover]
#[verifier::exec_allows_no_decreases_clause]
pub fn serv_main(cpu_index: usize) {
    if cpu_index == 0 {
        let (this_cpu, Tracked(mut perm)) = DekoCpuCtx::this_cpu();
        let cpu_nums: u64 = match CPU_NUM.get() {
            Some(DekoAtomicData { data, .. }) => data.num,
            None => 1,
        };

        kinfo!("Boot CPU: total CPU count = ", cpu_nums);

        let rq = this_cpu.borrow(Tracked(&perm.ptr_perm)).run_queue.as_ref();
        let vm = this_cpu.borrow(Tracked(&perm.ptr_perm)).vm_region.as_ref();
        kpanic_if!(
            core::hint::unlikely(rq.is_none() || vm.is_none()),
            "Current CPU has no run queue or VM region assigned.",
        );

        let rq = rq.as_ref().unwrap();

        let current =
            deko_rwlock_read_atomic_data! {
            rq,
            runqueue,
            __,
            {
                kpanic_if!(
                    core::hint::unlikely(runqueue.current.is_none()),
                    "Run queue is not well-formed.",
                );

                runqueue.current.as_ref().unwrap().clone()
            }
        };

        for i in 1..cpu_nums
            invariant
                1 <= i <= cpu_nums,
                cpu_nums <= CPUID_MAX_COUNT as u64,
                perm.wf_with(this_cpu),
                perm.ptr_perm.value().run_queue_spec() matches Some(rq_val) && rq_val.wf(),
                perm.ptr_perm.value().vm_region_spec() matches Some(vm_val) && vm_val.wf(),
                current.wf(),
            decreases cpu_nums - i,
        {
            proof_with!(Tracked(perm) => Tracked(new_perm));
            let serv_task = DekoRunnable::new(
                this_cpu,
                DekoTaskArgs {
                    entry: serv_main_func_ptr(),
                    name: "serv_main_ap",
                    mode: DekoTaskMode::Kernel {
                        entry: serv_main_func_ptr(),
                        param: i,
                        ret: run_kernel_tasks_func_ptr(),
                    },
                    parent: Some(current.clone()),  // spawned by the current task.
                },
            );

            kinfo!("Creating service main task for AP core ", i);
            // Set service main for other APs.
            // But this task never gets run?????
            DekoCpuCtx::start_kernel_task(this_cpu, Tracked(&mut new_perm), serv_task);

            kinfo!("Spawned service main on AP core ", i);
            proof {
                perm = new_perm;
            }
        }
    } else {
        // Migrate the task to self.
        set_cpu_affinity(cpu_index);
    }

    wait_ipi_blocking();  // ensure all cores are synchronized.

    let mut r = 0;

    // Try to enter the guest again.
    #[verus_spec(
        invariant
            cpu_index < CPUID_MAX_COUNT,
    )]
    loop {
        match try_enter_guest(r) {
            // The core does not have a guest created yet.
            // let it enter idle state.
            DekoGuestExitInformation::CoreNotCreated => {
                cpu_go_idle(cpu_index);
            },
            DekoGuestExitInformation::VmplSwitchFailed => {
                kerror!("VMPL switch failed on core ", cpu_index);
                die("VMPL switch failed.");
            },
            DekoGuestExitInformation::ServiceRequest { protocol, req, mut params } => {
                let (this_cpu, Tracked(mut perm)) = DekoCpuCtx::this_cpu();
                let this_cpu_id = this_cpu.borrow(Tracked(&perm.ptr_perm)).cpu_id as usize;
                kpanic_if!(
                    core::hint::unlikely(this_cpu_id != cpu_index),
                    "CPU ID mismatch when handling guest exit."
                );

                match #[verus_spec(with Tracked(&mut perm))]
                crate::guest::handle_guest_exit(protocol, req, &mut params, cpu_index as u64) {
                    Ok(()) => {
                        r = 0;
                    },
                    Err(e) => {
                        match e {
                            DekoGuestServError::FatalError => {
                                die("Fatal error occurred when handling guest request.");
                            },
                            DekoGuestServError::SoftError(e) => {
                                r = e.into_error_code();
                            },
                        }
                    },
                }
            },
        }
    }
}

func_ptr!(serv_main);

/// Attempts to transfer control to the Guest VM.
///
/// This function acts as the primary "World Switch" loop for the kernel. Its
/// purpose is to execute the VMRUN (or equivalent) instruction to run the
/// guest code. Upon a generic VM exit, it handles necessary housekeeping
/// and immediately attempts to re-enter the guest.
///
/// This function is called by [`serv_main`] after the scheduling environment.
/// Sometimes when we finish serving the VM exits, we want to re-enter the guest
/// immediately without going back to the scheduler.
///
/// This function never returns as the control flow must be implicitly transferred
/// to the guest context and it can request anything via VM exits.
#[verifier::exec_allows_no_decreases_clause]
#[verus_spec(
)]
pub fn try_enter_guest(prev_errno: u64) -> DekoGuestExitInformation {
    kinfo!("Attempting to enter guest...");

    let (this_cpu_ptr, Tracked(this_cpu_perm)) = DekoCpuCtx::this_cpu();
    let this_cpu = this_cpu_ptr.borrow(Tracked(&this_cpu_perm.ptr_perm));
    let this_cpu_index: usize = this_cpu.cpu_id as usize;
    if this_cpu.doorbell.is_none() {
        die("No doorbell assigned to the CPU.");
    }
    let Tracked(mut this_cpu_perm) = DekoCpuCtx::update_guest_vmsa(
        this_cpu_ptr,
        Tracked(this_cpu_perm),
    );

    proof_with!(Tracked(&this_cpu_perm) => Tracked(mut vmsa_perm));
    let vmsa = VMSA::this_vmsa(this_cpu_ptr);

    // This carries the request served by the monitor.
    // So we need to update rax to indicate whether the
    // request has been served successfully.
    proof_with!(Tracked(&mut vmsa_perm));
    VMSA::set_rax(vmsa, prev_errno);

    #[verus_spec(
        invariant
            this_cpu_index < CPUID_MAX_COUNT,
            this_cpu_perm.wf_with(this_cpu_ptr),
            this_cpu_perm.ptr_perm.value().doorbell is Some,
    )]
    loop {
        let cpu = this_cpu_ptr.borrow(Tracked(&this_cpu_perm.ptr_perm));
        let should_end =
            deko_rwlock_read_atomic_data! {
            PERCPU_AREAS,
            percpu_areas,
            __,
            {
                crate::check_shared_cpu_idx!(this_cpu_index as usize, percpu_areas, percpu_areas);

                let vmsa_ref = &percpu_areas.0[this_cpu_index].guest_vmsa;

                deko_rwlock_read_atomic_data! {
                    vmsa_ref,
                    vmsa,
                    vmsa_perm,
                    {
                        let mut should_end = true;
                        // If no caa found then this is meaningless and
                        // we just ignore the request.
                        if let Some(caa_addr) = vmsa.caa {
                            if let Some(vmsa_addr) = vmsa.vmsa {
                                proof_decl! {
                                    let tracked mut this_vmsa_perm;
                                }

                                let vmsa =
                                #[verus_spec(with Tracked(&this_cpu_perm) => Tracked(mut this_vmsa_perm))]
                                VMSA::this_vmsa(this_cpu_ptr);

                                #[verus_spec(with Tracked(&mut this_vmsa_perm))]
                                VMSA::enable(vmsa);

                                should_end = false;
                            }
                        }

                        should_end
                    }
                }
            }
        };

        // The lock is released early here.

        if should_end {
            return DekoGuestExitInformation::CoreNotCreated;
        }
        let r = no_irq_zone(
            ||
                {
                    // Also need to update the guest interrupt delivery information here.
                    // TODO: apic controller update.
                    // Need to update the guest APIC status here so no interrupt will
                    // be delivered.
                    // flush_tlb_global_sync();
                    let no_further_signal =
                        deko_rwlock_read_atomic_data! {
                            cpu.doorbell.as_ref().unwrap(),
                            doorbell,
                            doorbell_perm,
                            {
                                #[verus_spec(with Tracked(doorbell_perm.borrow()))]
                                HVDoorbell::no_further_signal(*doorbell)
                            }
                    };

                    if no_further_signal {
                        let r = vmpl_switch(2);  // switch to VMPL2
                        // crate::imp::vmpl_run(2);

                        if r != 0 {
                            kerror!("Failed to switch to VMPL2: error code ", r => hex);
                        }
                        r
                        // Now we need to read the VMSA to fetch the
                        // information process the guest's request.

                    } else {
                        1
                    }
                },
        );

        let new_perm = DekoCpuCtx::update_guest_vmsa(this_cpu_ptr, Tracked(this_cpu_perm));
        let Tracked(new_perm) = new_perm;

        proof {
            this_cpu_perm = new_perm;
        }

        if r != 0 {
            return DekoGuestExitInformation::VmplSwitchFailed;
        }
        // At this point we need to disable VMSA to prevent any
        // accidental VM entry.

        proof_decl! {
            let tracked mut this_vmsa_perm;
        }

        let vmsa = #[verus_spec(with Tracked(&this_cpu_perm) => Tracked(mut this_vmsa_perm))]
        VMSA::this_vmsa(this_cpu_ptr);

        #[verus_spec(with Tracked(&mut this_vmsa_perm))]
        VMSA::disable(vmsa);

        // If r == 0 then we have successfully entered the guest
        // and now we are back due to a VM exit.
        //
        // Now we parse the information.
        if let Some(info) = DekoGuestExitInformation::get_guest_exit_information() {
            return info;
        }
    }
}

} // verus!
