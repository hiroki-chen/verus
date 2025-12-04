use core::cmp::Ordering;
use core::sync::atomic::{AtomicU32, AtomicU64};

use deko_macros::DekoDebug;
use deko_std::address::{VaddrRange, VirtAddr};
use deko_std::array::Array;
use deko_std::cpu::{no_irq_zone, CpuID, X86GeneralRegs};
use deko_std::list::{LinkedList, Node};
use deko_std::mem::PAGE_SIZE;
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::sync::arc::DekoArc;
use deko_std::sync::rwlock::{DekoRwLock, RwLockPredicate};
use deko_std::sync::DekoAtomicData;
use deko_std::wf::WellFormed;
use deko_std::{boxed_ptr, with_permission};
use vstd::prelude::*;
use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl, PartialOrdSpecImpl};

use crate::collections::Vec;
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::mm::paging::{PageTable, PageTablePermission};
use crate::mm::vm::{
    VirtualMemoryRegion, VirtualMemoryRegionPermission, VirtualMemoryRegionPredicate,
};
use crate::mm::DEKO_FRAME_ALLOCATOR;
use crate::{die, kerror, kunimplemented};

verus! {

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
    const ID_COUNTER: AtomicU64 = AtomicU64::new(1);

    let mut id = ID_COUNTER.fetch_add(1, core::sync::atomic::Ordering::SeqCst);
    while id < 2 {
        id = ID_COUNTER.fetch_add(1, core::sync::atomic::Ordering::SeqCst);
    }

    id
}

/// The predicate for the global run queue that:
///
/// - Ensures the run queue is well-formed.
/// - Ensures its associated permission type is well-formed with respect to the run queue.
pub struct DekoRunqueuePred;

pub exec static DEKO_TASK_LIST: DekoRwLock<DekoRunQueue, DekoRunQueuePermission, DekoRunqueuePred> =
    {
    let (queue, Tracked(queue_perm)) = DekoRunQueue::new();

    DekoRwLock::new(
        DekoAtomicData { data: queue, perm: Tracked(queue_perm) },
        (),
        Ghost(DekoRunqueuePred {  }),
    )
};

impl RwLockPredicate<DekoAtomicData<DekoRunQueue, DekoRunQueuePermission>> for DekoRunqueuePred {
    #[verifier::inline]
    open spec fn inv(self, data: DekoAtomicData<DekoRunQueue, DekoRunQueuePermission>) -> bool {
        &&& data.data.wf()
        &&& data.data.wf_with(data.perm@)
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
    pub run_list: LinkedList<DekoPPtr<DekoRunnable>>,
    /// The currently running task.
    pub current: Option<DekoPPtr<DekoRunnable>>,
    /// The idle task pointer.
    pub idle: Option<DekoPPtr<DekoRunnable>>,
    /// The terminated task pointer.
    pub terminated: Option<DekoPPtr<DekoRunnable>>,
}

with_permission!(
    DekoRunQueue,
    run_list_perm: Ghost<Seq<DekoPointsTo<DekoRunnable>>>,
    current_ptr: Option<DekoPointsTo<DekoRunnable>>,
    idle_ptr: Option<DekoPointsTo<DekoRunnable>>,
    terminated_ptr: Option<DekoPointsTo<DekoRunnable>>,
);

impl WellFormed for DekoRunQueue {
    open spec fn wf(&self) -> bool {
        &&& self.run_list.wf()
    }
}

#[verus_verify]
impl DekoRunQueue {
    pub open spec fn wf_with(&self, perm: DekoRunQueuePermission) -> bool {
        &&& self.wf()
        &&& perm.run_list_perm@.len() == self.run_list@.len()
        &&& forall|i: int|
            #![trigger self.run_list@[i as int], perm.run_list_perm@[i as int]]
            0 <= i < perm.run_list_perm@.len() ==> self.run_list@[i as int]@
                == perm.run_list_perm@[i as int].pptr()
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

    /// Sets the idle task of the run queue; if there was a previous idle task,
    /// the task pointer is returned.
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut DekoRunQueuePermission>,
            Tracked(idle_perm): Tracked<DekoPointsTo<DekoRunnable>>,
        requires
            old(self).wf_with(*old(perm)),
            old(self).run_list@.len() < usize::MAX - 1,
            idle_perm.is_init(),
            idle_perm.wf(),
            idle_perm.pptr() == idle@,
        ensures
            self.run_list@ =~= old(self).run_list@.insert(0, idle),
            self.wf_with(*perm),
            match old(self).idle {
                None => r == None::<DekoPPtr<DekoRunnable>>,
                Some(old_idle) => r == Some(old_idle),
            },
            self.idle == Some(idle),
    )]
    pub fn set_idle_task(&mut self, idle: DekoPPtr<DekoRunnable>) -> Option<
        DekoPPtr<DekoRunnable>,
    > {
        let (idle_node_ptr, Tracked(mut idle_ptr_perm)) =
            boxed_ptr!(Node<DekoPPtr<DekoRunnable>>, &DEKO_FRAME_ALLOCATOR.0);
        // write something into the node.
        idle_node_ptr.write(
            Tracked(&mut idle_ptr_perm),
            Node { prev: None, next: None, value: idle },
        );
        self.run_list.push_front_no_alloc(idle_node_ptr, Tracked(idle_ptr_perm));
        proof {
            perm.run_list_perm@ = perm.run_list_perm@.insert(0, idle_perm);
        }

        // Update the global task list too.
        let (DekoAtomicData { mut data, perm: Tracked(mut perm) }, handle) =
            DEKO_TASK_LIST.acquire_write();
        proof {
            assert(data.wf_with(perm));
            assert(data.run_list.wf());
        }

        if data.run_list.len() >= usize::MAX - 1 {
            handle.release_write(DekoAtomicData { data, perm: Tracked(perm) });
            kerror!("Too many tasks in the system");
            die("");
        }
        let (idle_node_ptr, Tracked(mut idle_ptr_perm)) =
            boxed_ptr!(Node<DekoPPtr<DekoRunnable>>, &DEKO_FRAME_ALLOCATOR.0);
        // write something into the node.
        idle_node_ptr.write(
            Tracked(&mut idle_ptr_perm),
            Node { prev: None, next: None, value: idle },
        );

        data.run_list.push_front_no_alloc(idle_node_ptr, Tracked(idle_ptr_perm));
        proof {
            perm.run_list_perm@ = perm.run_list_perm@.insert(0, idle_perm);
        }

        handle.release_write(DekoAtomicData { data, perm: Tracked(perm) });
        self.idle.replace(idle)
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
#[repr(C, packed)]
#[derive(Clone, DekoDebug)]
pub struct DekoRunnableCtx {
    pub rsp: u64,
    pub regs: X86GeneralRegs,
    pub flags: u64,
    pub ret: u64,
}

/// A [`DekoRunnable`] represents a task that can be scheduled by the
/// task scheduler.
///
/// This is OS-level process. Each process will have several sub-processes/threads.
#[derive(DekoDebug)]
pub struct DekoRunnable {
    /// The stack pointer of the task.
    pub rsp: u64,
    /// The SSP of the task.
    pub ssp: VirtAddr,
    /// The unique id of the task.
    pub id: u64,
    /// The priority of the task.
    pub priority: u8,
    /// The page table of the task.
    pub pgtable: DekoRwLock<DekoPPtr<PageTable>, PageTablePermission, DekoPagaTablePred>,
    /// The stack owned by the task.
    pub stack: VaddrRange,
    /// The area allocated for XSAVE/XSTOR.
    pub xsave: DekoPPtr<Array<u8, 4096>>,
    /// The size of the XSAVE area.
    pub xsave_size: usize,
    /// The memory management.
    #[deko(skip)]
    pub mm: DekoArc<
        VirtualMemoryRegion,
        VirtualMemoryRegionPermission,
        VirtualMemoryRegionPredicate,
    >,
}

// todo: design this struct.
with_permission!(
    DekoRunnable,
    // parent_cpu: DekoCpuCore,
);

#[verus_verify]
impl DekoRunnable {
    /// Creates a new runnable task on the given CPU.
    #[verus_spec(r =>
        with
            Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
                -> runnable_perm: Tracked<DekoRunnablePermission>,
        requires
            old(ctx_perm).wf_with(cpu),
        ensures
            ctx_perm.wf_with(cpu),
    )]
    pub fn new(
        cpu: DekoPPtr<DekoCpuCtx>,
        entry: u64,
        parent: Option<DekoPPtr<DekoRunnable>>,  // in case of fork
    ) -> Self {
        let id = generate_id();
        let xsave_area_size = CpuID::xsave_area_size();
        // Allocate the XSAVE area.
        let (xsave_ptr, Tracked(xsave_perm)) = boxed_ptr!(Array<u8, 4096>, &DEKO_FRAME_ALLOCATOR.0);

        proof {
            assert(xsave_area_size <= PAGE_SIZE);
        }

        // We need to clone the page table.
        kunimplemented!("Implement DekoRunnable::new");
    }
}

impl WellFormed for DekoRunnable {
    open spec fn wf(&self) -> bool {
        &&& self.rsp % 8 == 0
        // &&& self.ssp@ % 8 == 0
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

/// Initializes the task scheduler.
///
/// This function will try to switch the current threat into the
/// the idle task and initializes the current task in the run.
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
                // need to fetch the pointer to the idle task
                // let idle_task = ???
            },
    );
}

/// Attempts to perform the task switch.
///
/// # Safety
///
/// The caller must ensure that both `pre` and `next`
/// are valid task pointers.
#[verus_spec(r =>
    )]
unsafe fn switch(pre: DekoPPtr<DekoRunnable>, next: DekoPPtr<DekoRunnable>) {
    // NO IRQ is allowed or the system will jump into
    // an inconsistent state.
    no_irq_zone(
        ||
            {
                let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();

                // perform the actual context switch
                // ???
            },
    );
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
        };

        (
            DekoRunQueue {
                run_list: LinkedList::new(),
                current: None,
                idle: None,
                terminated: None,
            },
            Tracked(perm),
        )
    }
}

} // verus!
