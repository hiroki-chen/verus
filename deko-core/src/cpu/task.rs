use core::cmp::Ordering;

use deko_macros::DekoDebug;
use deko_std::address::VirtAddr;
use deko_std::cpu::no_irq_zone;
use deko_std::list::LinkedList;
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::wf::WellFormed;
use deko_std::with_permission;
use vstd::prelude::*;
use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl, PartialOrdSpecImpl};

use crate::cpu::DekoCpuCtx;
use crate::mm::paging::PageTable;

verus! {

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
pub struct DekoRunQueue {
    /// The list of runnable tasks queued for execution.
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

    /// Creates a new, empty run queue.
    #[inline]
    #[verus_spec(r =>
        with
            -> perm: Tracked<DekoRunQueuePermission>,
        ensures
            r.wf(),
            r.wf_with(perm@),
            !r.is_scheduleable(),
    )]
    pub fn new() -> Self {
        proof_with!(|=
           Tracked(DekoRunQueuePermission {
                run_list_perm: Ghost(Seq::empty()),
                current_ptr: None,
                idle_ptr: None,
                terminated_ptr: None,
            }
        ));
        DekoRunQueue { run_list: LinkedList::new(), current: None, idle: None, terminated: None }
    }
}

/// A `[DekoRunnable`]` represents a task that can be scheduled by the
/// task scheduler.
#[derive(DekoDebug)]
pub struct DekoRunnable {
    /// The stack pointer of the task.
    pub rsp: u64,
    /// The SSP of the task.
    pub ssp: VirtAddr,
    /// The UUID of the task.
    pub uuid: [u8; 16],
    /// The priority of the task.
    pub priority: u8,
    /// The page table of the task.
    pub pgtable: DekoPPtr<PageTable>,
}

#[verus_verify]
impl DekoRunnable {

}

impl WellFormed for DekoRunnable {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl PartialEq for DekoRunnable {
    #[verifier::external_body]  // haven't figured out how to say this.
    fn eq(&self, other: &Self) -> bool {
        self.uuid == other.uuid
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
        self.uuid.eq_spec(&other.uuid)
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
