use core::cmp::Ordering;
use core::sync::atomic::{AtomicU32, AtomicU64};

use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::address::{VaddrRange, VirtAddr};
use deko_std::array::Array;
use deko_std::cpu::{no_irq_zone, CpuID, X86GeneralRegs};
use deko_std::list::{LinkedList, Node};
use deko_std::mem::{PAGE_SIZE, PGTABLE_LVL3_IDX_SHARED};
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::sync::arc::DekoArc;
use deko_std::sync::rwlock::{DekoRwLock, RwLockPredicate};
use deko_std::sync::{DekoAtomicData, RwLock};
use deko_std::wf::WellFormed;
use deko_std::{boxed_ptr, with_permission};
use vstd::prelude::*;
use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl, PartialOrdSpecImpl};

use crate::collections::Vec;
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::mm::paging::{PageTable, PageTablePermission};
use crate::mm::stack::DekoKernelStack;
use crate::mm::vm::{VirtualMemoryRegion, VirtualMemoryRegionPermission, VirtualMemoryRegionPred};
use crate::mm::DEKO_FRAME_ALLOCATOR;
use crate::{die, kerror, kpanic_if, kunimplemented};

verus! {

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
with_atomic_pred! {
    DekoRunQueue,
    DekoRunQueuePermission,
    fields: { },
    perm_fields: { },
    data.wf() && data.wf_with(perm)
}

pub exec static DEKO_TASK_LIST: DekoRwLock<DekoRunQueue, DekoRunQueuePermission, DekoRunQueuePred> =
    {
    let (queue, Tracked(queue_perm)) = DekoRunQueue::new();

    DekoRwLock::new(
        DekoAtomicData { data: queue, perm: Tracked(queue_perm) },
        (),
        Ghost(DekoRunQueuePred {  }),
    )
};

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
        &&& self.parent matches Some(parent) ==> parent.wf() && parent@.data.mm.wf()
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

    /// Sets the idle task of the run queue; if there was a previous idle task,
    /// the task pointer is returned.
    #[allow(non_shorthand_field_patterns)]
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut DekoRunQueuePermission>,
        requires
            old(self).wf_with(*old(perm)),
            old(self).run_list@.len() < usize::MAX - 1,
            idle.wf(),
        ensures
            self@ =~= old(self)@.insert(0, idle@),
            self.wf_with(*perm),
            match old(self).idle {
                None => r == None::<DekoRunnablePtr>,
                Some(old_idle) => r == Some(old_idle),
            },
            self.idle == Some(idle),
    )]
    pub fn set_idle_task(&mut self, idle: DekoRunnablePtr) -> Option<DekoRunnablePtr> {
        proof {
            use_type_invariant(&idle);
        }

        let (idle_node_ptr, Tracked(mut idle_ptr_perm)) =
            boxed_ptr!(Node<DekoRunnablePtr>, &DEKO_FRAME_ALLOCATOR.0);

        // write something into the node.
        idle_node_ptr.write(
            Tracked(&mut idle_ptr_perm),
            Node { prev: None, next: None, value: idle.clone() },
        );
        self.run_list.push_front_no_alloc(idle_node_ptr, Tracked(idle_ptr_perm));
        proof {
            perm.run_list_perm@ = perm.run_list_perm@.insert(0, Ghost(idle));
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
            boxed_ptr!(Node<DekoRunnablePtr>, &DEKO_FRAME_ALLOCATOR.0);
        // write something into the node.
        idle_node_ptr.write(
            Tracked(&mut idle_ptr_perm),
            Node { prev: None, next: None, value: idle.clone() },
        );

        data.run_list.push_front_no_alloc(idle_node_ptr, Tracked(idle_ptr_perm));
        proof {
            perm.run_list_perm@ = perm.run_list_perm@.insert(0, Ghost(idle));
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
    pub mm: DekoArc<VirtualMemoryRegion, VirtualMemoryRegionPermission, VirtualMemoryRegionPred>,
}

#[verus_verify]
impl DekoRunnable {
    /// Createas and initializes a new virtual memory manager for the task.
    #[verus_spec(r =>
        ensures
            r.wf(),
    )]
    pub fn create_mm() -> DekoArc<
        VirtualMemoryRegion,
        VirtualMemoryRegionPermission,
        VirtualMemoryRegionPred,
    > {
        kunimplemented!()
    }

    #[verus_spec(r =>
        with
            Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
            Tracked(xsave_perm): Tracked<&DekoPointsTo<Array<u8, 4096>>>,
        requires
            old(ctx_perm).wf_with(cpu),
            xsave@ == xsave_perm.pptr(),
        ensures
            ctx_perm.wf_with(cpu),
            ctx_perm.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
    )]
    pub fn alloc_user_stack(
        cpu: DekoPPtr<DekoCpuCtx>,
        entry: u64,
        xsave: DekoPPtr<Array<u8, 4096>>,
    ) -> (VaddrRange, VaddrRange, u64) {
        kunimplemented!()
    }

    /// Returns the stack mapped range, the raw stack range, and the initial RSP value.
    #[verus_spec(r =>
        with
            Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
            Tracked(xsave_perm): Tracked<&DekoPointsTo<Array<u8, 4096>>>,
        requires
            old(ctx_perm).wf_with(cpu),
            xsave@ == xsave_perm.pptr(),
        ensures
            ctx_perm.wf_with(cpu),
            ctx_perm.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
    )]
    pub fn alloc_kernel_stack(
        cpu: DekoPPtr<DekoCpuCtx>,
        entry: u64,
        param: u64,
        ret: u64,
        xsave: DekoPPtr<Array<u8, 4096>>,
    ) -> (VaddrRange, VaddrRange, u64) {
        let stack = DekoKernelStack::new_with_size(0x8000, false);
        let range = stack.range();

        // We need to setup a context on the stack that matches the stack layout
        // defined in switch_context below.

        kunimplemented!()
    }

    /// Creates a new runnable task with the given arguments on the given CPU.
    #[verus_spec(r =>
        with
            Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
        requires
            old(ctx_perm).wf_with(cpu),
            old(ctx_perm).ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
            args.wf(),
        ensures
            r.wf(),
            ctx_perm.wf_with(cpu),
            ctx_perm.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
            // r@.???
    )]
    pub fn new(cpu: DekoPPtr<DekoCpuCtx>, args: DekoTaskArgs) -> DekoRunnablePtr {
        let cpu_borrowed = cpu.borrow(Tracked(&ctx_perm.ptr_perm));

        kpanic_if!(core::hint::unlikely(
            cpu_borrowed.vm_region().is_none(),
        ), "CPU has no VM region assigned");

        // Allocate a page table for the new task.
        let (new_pgtable, _, Tracked(mut pgtable_perm)) = PageTable::new(
            cpu_borrowed.private_bit,
            cpu_borrowed.shared_bit,
            Ghost(&cpu_borrowed.kernel_mapping_spec()),
        );

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

        proof_with!(Tracked(&mut pgtable_perm));
        cpu_borrowed.vm_region().as_ref().unwrap().copy_to_page_table(new_pgtable);

        let task_mm = match args.parent {
            Some(ptr) => { ptr.as_ref().data.mm.clone() },
            None => { Self::create_mm() },
        };

        // Allocate xsave areas.
        let (xsave_ptr, Tracked(xsave_perm)) = boxed_ptr!(Array<u8, 4096>, &DEKO_FRAME_ALLOCATOR.0);
        // This does nothing but clear the area to mark it as init.
        xsave_ptr.put(Tracked(&mut xsave_perm), Array::fill(0));

        let (stack, vrange, rsp) = match args.mode {
            DekoTaskMode::Kernel { entry, param, ret } => {
                proof_with!(Tracked(ctx_perm), Tracked(&xsave_perm));
                Self::alloc_kernel_stack(cpu, entry, param, ret, xsave_ptr)
            },
            DekoTaskMode::User { entry } => {
                proof_with!(Tracked(ctx_perm), Tracked(&xsave_perm));
                Self::alloc_user_stack(cpu, entry, xsave_ptr)
            },
        };

        let task = DekoRunnable {
            id: generate_id(),
            pgtable: RwLock::new(
                DekoAtomicData::new_with(new_pgtable, Tracked(pgtable_perm)),
                (),
                Ghost(DekoPagaTablePred {  }),
            ),
            priority: 0,
            xsave: xsave_ptr,
            mm: task_mm,
            rsp: vrange.end.0.checked_sub(rsp).unwrap_or(0),
            ssp: VirtAddr(0),
            stack,
            xsave_size: PAGE_SIZE as _,
        };

        proof {
            // need to fix it later.
            assert(task.wf()) by {
                admit();
            }
        }

        DekoArc::new(
            DekoAtomicData::new_with(task, Tracked(DekoRunnablePermission { xsave_perm })),
            &DEKO_FRAME_ALLOCATOR.0,
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
unsafe fn switch(pre: DekoRunnablePtr, next: DekoRunnablePtr) {
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
