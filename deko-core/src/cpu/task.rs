use core::cmp::Ordering;
use core::ops::{Add, Range};
use core::sync::atomic::{AtomicU32, AtomicU64};

use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::address::{MappingSpace, VaddrRange, VirtAddr};
use deko_std::array::Array;
use deko_std::bits::bit_u64_and_auto;
use deko_std::cpu::{no_irq_zone, CpuID, X86GeneralRegs};
use deko_std::list::{LinkedList, Node};
use deko_std::mem::bitalloc::{DekoBitAlloc, DekoBitmapAllocator1024};
use deko_std::mem::{PAGE_SIZE, PERTASK_BASE, PGTABLE_LVL3_IDX_SHARED};
use deko_std::misc::early_dbg;
use deko_std::prelude::{func_ptr, VADDR_UPPER_MASK};
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::sync::arc::DekoArc;
use deko_std::sync::rwlock::{DekoRwLock, RwLockPredicate};
use deko_std::sync::{DekoAtomicData, DekoSimpleRwLock, DekoSimpleRwLockPred, RwLock};
use deko_std::wf::WellFormed;
use deko_std::{boxed_ptr, with_permission, TrivialPredicate};
use vstd::prelude::*;
use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl, PartialOrdSpecImpl};

use crate::collections::Vec;
use crate::cpu::irq::irq_enable;
use crate::cpu::regs::sse_restore_context;
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission, CPUID_MAX_COUNT};
use crate::mm::frame_allocator::DekoPageFrameAllocator;
use crate::mm::paging::{
    bit_not_in_addr_region, bit_not_overlapping, PageTable, PageTablePermission, PteFlags,
};
use crate::mm::stack::DekoKernelStack;
use crate::mm::vm::{
    self, VirtualMemory, VirtualMemoryPermission, VirtualMemoryRegion,
    VirtualMemoryRegionPermission, VirtualMemoryRegionPred, VmMapping, VmMappingPred, VMR_GRANULE,
};
use crate::mm::{virt_to_phys, DEKO_FRAME_ALLOCATOR};
use crate::{die, kerror, kinfo, kpanic_if, kunimplemented};

core::arch::global_asm!(include_str!("switch.S"), options(att_syntax));

verus! {

pub exec static DEKO_KTASK_BIT_ALLOC: DekoSimpleRwLock<DekoBitmapAllocator1024>
    ensures
        DEKO_KTASK_BIT_ALLOC.wf(),
{
    let allocator = DekoBitmapAllocator1024::new_empty();
    let r = DekoSimpleRwLock::new(
        DekoAtomicData::new(allocator),
        (),
        Ghost(TrivialPredicate::new()),
    );

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
    let (mut alloc, write_handle) = DEKO_KTASK_BIT_ALLOC.acquire_write();

    let r = alloc.data.alloc(1, 0);
    write_handle.release_write(alloc);

    match r {
        None => None,
        Some(idx) => {
            // HACK: for testing purposes.
            let idx = 1;
            let span = 0x8000000000u64 / DekoBitmapAllocator1024::cap() as u64;
            let base = PERTASK_BASE.0 + (idx * span as usize) as u64;

            Some((idx, VirtAddr(base)..VirtAddr(span as u64 + base)))
        },
    }
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
    const ID_COUNTER: AtomicU64 = AtomicU64::new(2);

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
    /// Someone put the task here so the current CPU
    /// must take care with it.
    pub wake: Option<DekoRunnablePtr>,
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
        &&& self.idle.wf()
        &&& self.terminated.wf()
        &&& self.wake.wf()
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
    )]
    pub fn schedule_init(&mut self) -> DekoRunnablePtr {
        if self.run_list.len() == 0 {
            match &self.idle {
                Some(idle_ptr) => {
                    self.current = Some(idle_ptr.clone());

                    idle_ptr.clone()
                },
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
            // todo: free the node.

            self.current = Some(task.clone());

            proof {
                perm.run_list_perm = Ghost(perm.run_list_perm@.remove(0));
            }

            task
        }
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
    #[deko(hex)]
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
    #[deko(hex)]
    pub xsave_size: usize,
    /// The memory management.
    pub mm: DekoArc<VirtualMemoryRegion, VirtualMemoryRegionPermission, VirtualMemoryRegionPred>,
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
            &DEKO_FRAME_ALLOCATOR.0,
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
            (*task_ctx_ptr).flags = 0x2;  // Default flags with interrupts enabled.

            (task_ctx_ptr as *mut u64).write(on_task_exit as u64);
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
    pub fn alloc_kernel_stack(
        vm_region: &mut VirtualMemoryRegion,
        private_bit: u64,
        shared_bit: u64,
        allocator: &DekoPageFrameAllocator,
        entry: u64,
        param: u64,
        ret: u64,
        xsave: DekoPPtr<Array<u8, 4096>>,
    ) -> (VirtAddr, Range<u64>, u64) {
        kinfo!("the vm region before allocating kernel stack: ", vm_region => hex);

        let mut stack = DekoKernelStack::new_with_size(0x8000, false);
        proof_with!(Tracked(pgtable_perm));
        stack.alloc_pages(private_bit, shared_bit, allocator);

        let range = stack.range();

        kinfo!("Allocated kernel stack at range: ", range => hex);

        let mapping = {
            let stack = VmMapping::Stack { stack };

            proof {
                assert(stack.mapping_size_spec() >= PAGE_SIZE) by {
                    assert(0x8000u64 >> 12 == 8) by (bit_vector);
                }
            }

            let mapping_lock = DekoRwLock::new(
                DekoAtomicData::new(stack),
                (),
                Ghost(VmMappingPred {  }),
            );

            proof {
                use_type_invariant(&mapping_lock);
            }

            DekoArc::new(
                DekoAtomicData::new(mapping_lock),
                &DEKO_FRAME_ALLOCATOR.0,
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

        kinfo!("Allocated kernel stack at virtual address: ", vaddr => hex);
        kinfo!("Kernel top of stack: ", stack_tos => hex);
        kinfo!("Kernel stack rsp: ", stack_ptr => hex);
        kinfo!("ret addr: ", ret => hex);

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
            args.wf(),
        ensures
            r.wf(),
            ctx_perm_updated@.wf_with(cpu),
            ctx_perm_updated@.ptr_perm.value().vm_region_spec() matches Some(vm) && vm.wf(),
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

        proof_with!(Tracked(&mut pgtable_perm), Tracked(&ctx_perm.vm_region_perm.tracked_borrow()));
        cpu_borrowed.vm_region().as_ref().unwrap().copy_to_page_table(new_pgtable);
        // Allocate xsave areas.
        let (xsave_ptr, Tracked(xsave_perm)) = boxed_ptr!(Array<u8, 4096>, &DEKO_FRAME_ALLOCATOR.0);
        // This does nothing but clear the area to mark it as init.
        xsave_ptr.put(Tracked(&mut xsave_perm), Array::fill(0));

        let tracked mut ctx_perm = ctx_perm;
        let cpu_taken = cpu.take(Tracked(&mut ctx_perm.ptr_perm));
        let DekoCpuCtx {
            magic,
            cpu_id,
            ghcb,
            tss,
            shared_area,
            pgtable,
            ctx_switch_stack,
            ist_stack,
            private_bit,
            shared_bit,
            kernel_mapping,
            vm_region,
            apic,
            run_queue,
        } = cpu_taken;
        kpanic_if!(core::hint::unlikely(
            vm_region.is_none(),
        ), "CPU has no VM region assigned");

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
                    &DEKO_FRAME_ALLOCATOR,
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

        let stack_bounds = VirtAddr(stack.0 + vrange.start)..VirtAddr(stack.0 + vrange.end);
        kinfo!("rsp offset is : ", rsp_offset => hex);

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
            rsp: stack_bounds.end.0.checked_sub(rsp_offset).unwrap_or(0),
            ssp: VirtAddr(0),
            stack: stack_bounds,
            xsave_size: PAGE_SIZE as _,
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
            shared_area,
            pgtable,
            ctx_switch_stack,
            ist_stack,
            private_bit,
            shared_bit,
            kernel_mapping,
            vm_region: Some(vm_region),
            apic,
            run_queue,
        };
        let tracked ctx_perm = DekoCpuCtxPermission {
            ptr_perm,
            pgtable_perm: cpu_pgtable_perm,
            ghcb_perm,
            vm_region_perm: Some(vm_region_perm),
        };
        cpu.write(Tracked(&mut ctx_perm.ptr_perm), cpu_new);

        kinfo!("Finished creating new task with ID: ", task.id => hex);

        proof_with!(|= Tracked(ctx_perm));
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
                let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();
                let cpu = cpu.borrow(Tracked(&perm.ptr_perm));

                match &cpu.run_queue {
                    Some(runqueue) => {
                        let (DekoAtomicData { data: mut runqueue, mut perm }, handle) =
                            runqueue.acquire_write();

                        kpanic_if!(!runqueue.is_scheduleable(),
                                   "No scheduleable task is found.");

                        proof_with!(Tracked(perm.borrow_mut()));
                        let task = runqueue.schedule_init();

                        proof {
                            use_type_invariant(&task);
                        }

                        handle.release_write(DekoAtomicData::new_with(runqueue, perm));

                        // perform the actual context switch
                        kinfo!("next task to schedule: ", task.as_ref().data);

                        switch(None, task);
                    },
                    None => {
                        die("No active run queue is found.");
                    },
                }
            },
    );
}

/// Attempts to perform the task switch.
#[verus_spec(r =>
    requires
        pre.wf(),
        next.wf(),
)]
fn switch(pre: Option<DekoRunnablePtr>, next: DekoRunnablePtr) {
    // NO IRQ is allowed or the system will jump into
    // an inconsistent state.
    no_irq_zone(
        ||
            {
                let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();
                let cpu = cpu.borrow(Tracked(&perm.ptr_perm));
                let Some(stack) = cpu.ctx_switch_stack else {
                    die("No context switch stack is assigned to the CPU.");
                };
                let private_bit = cpu.private_bit;
                let shared_bit = cpu.shared_bit;

                kinfo!("the private_bit: ", private_bit => hex);
                kinfo!("the shared_bit: ", shared_bit => hex);

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
                unsafe {
                    do_context_switch(pre, next, deko_rsp_offset(), cr3_next, stack.0);
                }
            },
    );
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
fn do_context_switch(pre: u64, next: u64, rsp_offset: u64, cr3_next: u64, stack_next: u64) {
    kinfo!("Switching context: pre=", pre => hex);
    kinfo!("Switching context: next=", next => hex);
    kinfo!("Switching context: cr3_next=", cr3_next => hex);
    kinfo!("Switching context: stack_next=", stack_next => hex);
    kinfo!("Switching context: rsp_offset=", rsp_offset => hex);

    // Debug what's stored at rsp of the next task.
    let rsp_arr: &[u64; 18] = unsafe {
        core::slice::from_raw_parts(
            ((next).add(rsp_offset) as *const u64).read() as *const u64,
            18,
        ).try_into().unwrap()
    };

    for (i, val) in rsp_arr.iter().enumerate() {
        kinfo!("rsp[", i, "] = ", *val => hex);
    }

    // kinfo!("Next task rsp content:", rsp_arr => hex);

    // test if rsp can be read.
    let v = unsafe { (((next as *const DekoRunnable).read().rsp) as *const u8).read() };

    unsafe {
        core::arch::asm!(
            "call context_switch",
            in("r11") rsp_offset,
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
    kinfo!("Trampoline: entered `run_kernel_tasks:`");
    kinfo!("\tentry = ", entry => hex);
    kinfo!("\txsave_addr = ", xsave_addr.addr() as u64 => hex);
    kinfo!("\tstart_params = ", start_params => hex);

    // Now we need to re-enable the interrupts.
    // Then we enter the entry.
    irq_enable();

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
    #[verus_spec(
        invariant
            which < CPUID_MAX_COUNT,
    )]
    loop {
        early_dbg();  // <=> hlt, though bad naming

        // Check if there is any IPI sent to this CPU.
        let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();
        let cpu = cpu.borrow(Tracked(&perm.ptr_perm));
    }
}

} // verus!
