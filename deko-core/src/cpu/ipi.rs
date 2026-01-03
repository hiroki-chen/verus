use core::ffi::c_void;
use core::marker::PhantomData;
use core::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use deko_macros::DekoDebug;
use deko_std::prelude::{func_ptr, DekoPointsTo};
use deko_std::ptr::DekoPPtr;
use deko_std::sync::{DekoAtomicData, DekoSimpleRwLock};
use deko_std::wf::WellFormed;
use deko_std::{
    deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data, func, with_permission,
};
use vstd::atomic::*;
use vstd::cell::{PCell, PointsTo};
use vstd::prelude::*;

use crate::cpu::apic::{Apic, X86Apic};
use crate::cpu::task::{schedule, DekoRunnablePtr, DekoRunnableState};
use crate::cpu::{
    flush_tlb_global_percpu, DekoCpuCtx, DekoCpuCtxPermission, PerCpuAreas, PerCpuAreasPermission,
    CPUID_MAX_COUNT, PERCPU_AREAS,
};
use crate::{die, kdebug, kinfo, kpanic_if, kwarn};

verus! {

pub exec static IPI_AVAILABLE_CPU_COUNT: AtomicUsize = AtomicUsize::new(1);

#[inline]
pub fn add_ipi_available_cpu() {
    IPI_AVAILABLE_CPU_COUNT.fetch_add(1, Ordering::SeqCst);
}

#[inline]
pub fn get_ipi_available_cpu_count() -> usize {
    IPI_AVAILABLE_CPU_COUNT.load(Ordering::SeqCst)
}

#[verifier::exec_allows_no_decreases_clause]
pub fn wait_ipi_blocking() {
    IPI_AVAILABLE_CPU_COUNT.fetch_sub(1, Ordering::SeqCst);
    while get_ipi_available_cpu_count() != 0 {
        core::hint::spin_loop();
    }
}

// global layout CpuIpiArea is 8;
const VECTOR_IPI: u32 = 0xe0;

const DELIVERY_MODE_FIXED: u32 = 0x0;

// Bits 10:8 = 000
const DEST_MODE_PHYSICAL: u32 = 0x0;

// Bit 11 = 0
const LEVEL_ASSERT: u32 = 0x4000;

// Bit 14 = 1
const TRIGGER_EDGE: u32 = 0x0;

// Bit 15 = 0
const DEST_SHORTHAND_NONE: u32 = 0x0;

/// A shared area for performing IPI communication between CPUs.
pub struct CpuIpiArea {
    /// The set the CPUs that have requested IPI handling by this CPU (max 32 for now).
    pub request_set: PAtomicU32,
    /// The numbers of remaining pending IPI requests.
    pub pending: PAtomicUsize,
    pub message: PCell<Option<DekoIpIMessage>>,
    // pub message: DekoSimpleRwLock<DekoIpIMessage>,
    pub handler: PCell<u64>,  // extern "C" fn(*const msg),
}

impl CpuIpiArea {
    /// Creates a new and empty [`CpuIpiArea`].
    pub const fn new() -> (r: (Self, Tracked<CpuIpiAreaPermission>))
        ensures
            r.1@.pending_perm.is_for(r.0.pending),
            r.1@.request_set_perm.is_for(r.0.request_set),
            r.1@.pending_perm.value() == 0,
            r.1@.handler_perm.id() == r.0.handler.id(),
            r.1@.message_perm.id() == r.0.message.id(),
            r.1@.message_perm.value() == None::<DekoIpIMessage>,
            r.1@.handler_perm.value() == 0,
            r.1@.message_perm.is_init(),
            r.1@.handler_perm.is_init(),
    {
        let (request_set, Tracked(request_set_perm)) = PAtomicU32::new(0);
        let (pending, Tracked(pending_perm)) = PAtomicUsize::new(0);
        let (message, Tracked(message_perm)) = PCell::new(None);
        let (handler, Tracked(handler_perm)) = PCell::new(0u64);

        (
            CpuIpiArea { request_set, pending, message, handler },
            Tracked(
                CpuIpiAreaPermission { request_set_perm, pending_perm, message_perm, handler_perm },
            ),
        )
    }
}

// Note that this permission is not core-exclusive because multiple CPUs
// may read/write to the IPI area concurrently. Thus, no CPUs will hold
// this but a global list of permissions will be maintained instead; only
// valid read/write access operations via the permissioned RwLocks can be
// performed to obtain the necessary access.
with_permission!(
    CpuIpiArea,
    request_set_perm: PermissionU32,
    pending_perm: PermissionUsize,
    message_perm: PointsTo<Option<DekoIpIMessage>>,
    handler_perm: PointsTo<u64>,
);

// Bits 19:18 = 00
/// Represents the different types of IPI messages.
#[derive(DekoDebug)]
pub enum DekoIpIMessage {
    /// A message to request a TLB shootdown.
    TlbShootdown,
    /// Affinity change message.
    AffinityChange {
        #[deko(skip)]
        task: DekoRunnablePtr,
    },
}

#[verus_verify]
impl DekoIpIMessage {
    #[verus_spec(r =>
        requires
            self.wf(),
        ensures
            r.wf(),
    )]
    pub fn clone(&self) -> Self {
        match self {
            DekoIpIMessage::TlbShootdown => DekoIpIMessage::TlbShootdown,
            DekoIpIMessage::AffinityChange { task } => DekoIpIMessage::AffinityChange {
                task: task.clone(),
            },
        }
    }
}

/// Represents an Inter-Processor Interrupt (IPI) request.
#[derive(DekoDebug)]
pub struct DekoIpiRequest {
    /// Bitmap of target CPUs; each bit represents a CPU.
    /// Bit 0 represents CPU 0, bit 1 represents CPU 1, and so on.
    ///
    /// Maximum number of CPUs supported is 32.
    pub targets: u32,
    /// The IPI message to send.
    pub message: DekoIpIMessage,
    /// Sender
    pub sender: usize,
}

impl WellFormed for DekoIpiRequest {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.message.wf()
    }
}

impl WellFormed for DekoIpIMessage {
    open spec fn wf(&self) -> bool {
        match self {
            DekoIpIMessage::TlbShootdown => true,
            DekoIpIMessage::AffinityChange { task } => task.wf(),
        }
    }
}

#[verus_verify]
impl DekoIpiRequest {
    #[verus_spec(r =>
        requires
            forall |i: int|
                0 <= i < targets.len() as int ==> #[trigger] targets@[i] < CPUID_MAX_COUNT,
            msg.wf(),
        ensures
            r.wf(),
    )]
    pub fn new(targets: &[usize], msg: DekoIpIMessage) -> Self {
        let mut bitmap: u32 = 0;

        for i in 0..targets.len()
            invariant
                0 <= i <= targets.len(),
                forall|j: int|
                    0 <= j < targets@.len() as int ==> #[trigger] targets@[j] < CPUID_MAX_COUNT,
        {
            let cpu_id = targets[i];
            bitmap |= 1 << cpu_id;
        }

        let (cpu, Tracked(cpu_perms)) = DekoCpuCtx::this_cpu();
        let sender = cpu.borrow(Tracked(&cpu_perms.ptr_perm)).cpu_id as usize;

        DekoIpiRequest { targets: bitmap, message: msg, sender }
    }

    /// &mut is not supported...
    #[verifier::external_body]
    #[verus_spec(
        with
            Tracked(cpu_areas_perm): Tracked<&mut PerCpuAreasPermission>,
        requires
            self.wf(),
            old(cpu_areas).wf_with(*old(cpu_areas_perm)),
            index < old(cpu_areas)@.len(),
        ensures
            cpu_areas.wf_with(*cpu_areas_perm),
    )]
    pub fn update_shared_area_ipi(
        &self,
        cpu_areas: &mut PerCpuAreas,
        index: usize,
        cpu_num: usize,
        f: usize,
    ) {
        let ipi_area = &mut cpu_areas.0[index].ipi_shared;

        // Increment the count of pending requests.
        ipi_area.pending.store(Tracked::assume_new(), cpu_num as _);
        ipi_area.message.put(Tracked::assume_new(), Some(self.message.clone()));
        ipi_area.handler.put(Tracked::assume_new(), f as u64);
    }

    /// Sends the IPI to the target CPUs.
    #[verifier::exec_allows_no_decreases_clause]
    #[verus_spec(
        requires
            self.wf(),
    )]
    pub fn send_ipi(&self) {
        kdebug!("Sending IPI from CPU", self.sender => hex, "to targets BITMAP", self.targets => hex);

        let (cpu, Tracked(cpu_perms)) = DekoCpuCtx::this_cpu();
        let id = cpu.borrow(Tracked(&cpu_perms.ptr_perm)).cpu_id as usize;
        let apic = &cpu.borrow(Tracked(&cpu_perms.ptr_perm)).apic;

        kpanic_if!(
            core::hint::unlikely(self.sender != id),
            "Sender ID mismatch: sender",
            id,
            "but recorded sender is ",
            self.sender,
        );

        let f = match &self.message {
            DekoIpIMessage::TlbShootdown => handle_tlb_shootdown_func_ptr() as usize,
            DekoIpIMessage::AffinityChange { .. } => handle_set_affinity_func_ptr() as usize,
        };

        // Prepare the message on the shared area so
        // other CPUs can read it when they receive the IPI.
        let mut cpu_nums = 0u32;
        let mut i = 0;
        #[verus_spec(
            invariant
                0 <= i <= CPUID_MAX_COUNT,
                self.wf(),
                cpu_nums <= i,
            decreases
                CPUID_MAX_COUNT - i,
        )]
        while i < CPUID_MAX_COUNT {
            if (self.targets & (1 << i)) != 0 {
                cpu_nums += 1;
            }
            i += 1;
        }

        deko_rwlock_write_atomic_data!(
            PERCPU_AREAS,
            cpu_areas,
            cpu_areas_perm,
            {
                // Obtain a reference to this CPU's IPI area.
                let Some(mut inner) = cpu_areas else {
                    die("PERCPU_AREAS is not initialized");
                };

                kpanic_if!(
                    core::hint::unlikely(id >= inner.0.len()),
                    "Target CPU ID",
                    id,
                    "exceeds current CPU count",
                    inner.0.len(),
                );

                #[verus_spec(with Tracked(cpu_areas_perm.borrow_mut()))]
                self.update_shared_area_ipi(
                    &mut inner,
                    id,
                    cpu_nums as usize,
                    f,
                );

                cpu_areas = Some(inner);
            }
        );

        i = 0;
        #[verus_spec(
            invariant
                0 <= i <= CPUID_MAX_COUNT,
            decreases
                CPUID_MAX_COUNT - i,
        )]
        while i < CPUID_MAX_COUNT {
            if (self.targets & (1 << i)) != 0 {
                // Now it is safe to send, because the receiver will
                // see the correct 'pending' count and message.
                send_ipi_to(i, apic);
            }
            i += 1;
        }

        // Now let's wait for others to complete their handling.
        #[verus_spec(
            invariant
                self.wf(),
                0 <= id < CPUID_MAX_COUNT,
        )]
        loop {
            core::hint::spin_loop();

            let pending =
                deko_rwlock_read_atomic_data!(
                PERCPU_AREAS,
                cpu_areas,
                cpu_areas_perm,
                {
                    let Some(ref cpu_areas) = cpu_areas else {
                        die("PERCPU_AREAS is not initialized");
                    };
                    kpanic_if!(
                        core::hint::unlikely(id >= cpu_areas.0.len()),
                        "Target CPU ID",
                        id,
                        "exceeds current CPU count",
                        cpu_areas.0.len(),
                    );

                    // Obtain a reference to this CPU's IPI area.
                    let ipi_area = &cpu_areas.0[id].ipi_shared;
                    let tracked ipi_area_perm = cpu_areas_perm.borrow().shared_perms.tracked_borrow(id as int);

                    ipi_area.pending.load(Tracked(&ipi_area_perm.ipi_shared_perm.pending_perm))
                }
            );

            if pending == 0 {
                break ;
            }
        }
    }
}

/// Helper function to send an IPI to specified CPUs.
#[verus_spec(
    requires
        target < CPUID_MAX_COUNT,
)]
fn send_ipi_to(target: usize, from: &X86Apic) {
    proof {
        assert((target as u64) << 32 <= u64::MAX) by (bit_vector)
            requires
                target < CPUID_MAX_COUNT,
        ;
    }

    let low = VECTOR_IPI | DELIVERY_MODE_FIXED | DEST_MODE_PHYSICAL | LEVEL_ASSERT | TRIGGER_EDGE
        | DEST_SHORTHAND_NONE;
    let high = (target as u32);

    kdebug!("Sending IPI", ((high as u64) << 32 | low as u64) => hex, "to target CPU", target => hex);

    deko_rwlock_write_atomic_data! {
        PERCPU_AREAS,
        cpu_areas,
        cpu_areas_perm,
        {
            let Some(ref cpu_areas) = cpu_areas else {
                die("PERCPU_AREAS is not initialized");
            };

            kpanic_if!(
                core::hint::unlikely(target >= cpu_areas.0.len()),
                "Target CPU ID",
                target,
                "exceeds current CPU count",
                cpu_areas.0.len(),
            );

            // Obtain a reference to the target CPU's IPI area.
            let ipi_area = &cpu_areas.0[target].ipi_shared;
            let tracked mut ipi_area_perm = cpu_areas_perm.borrow_mut().shared_perms.tracked_remove(target as int);

            // Mark that an IPI request has been made to the target CPU.
            ipi_area.request_set.fetch_or(Tracked(&mut ipi_area_perm.ipi_shared_perm.request_set_perm), (1 << from.id()));

            proof {
                cpu_areas_perm.borrow_mut().shared_perms.tracked_insert(target as int, ipi_area_perm);
            }
        }
    };

    let from_id = from.id();
    from.icr_write(low, high);
}

#[verus_verify]
impl DekoCpuCtx {
    /// Handles an incoming IPI request received.
    #[verus_spec(
        with
            Tracked(cpu_perm): Tracked<&DekoCpuCtxPermission>,
        requires
            cpu_perm.wf_with(ptr),
    )]
    pub fn handle_ipi_req(ptr: DekoPPtr<Self>) {
        let cpu_borrowed = ptr.borrow(Tracked(&cpu_perm.ptr_perm));
        let cpu_id = cpu_borrowed.cpu_id as usize;

        // First quickly grab the set of CPUs that have requested IPIs.
        let cpu_set =
            deko_rwlock_read_atomic_data! {
            PERCPU_AREAS,
            cpu_areas,
            cpu_areas_perm,
            {
                let Some(ref cpu_areas) = cpu_areas else {
                    die("PERCPU_AREAS is not initialized");
                };

                kpanic_if!(
                    core::hint::unlikely(cpu_id >= cpu_areas.0.len()),
                    "Target CPU ID",
                    cpu_id,
                    "exceeds current CPU count",
                    cpu_areas.0.len(),
                );

                let tracked ipi_perm = cpu_areas_perm.borrow().shared_perms.tracked_borrow(cpu_id as int);
                let ipi_area = &cpu_areas.0[cpu_id].ipi_shared;
                ipi_area.request_set.load(Tracked(&ipi_perm.ipi_shared_perm.request_set_perm)).clone()
            }
        };

        for i in 0..CPUID_MAX_COUNT {
            if (cpu_set & (1 << i)) != 0 {
                // Now we must handle the IPI from CPU i; this requires us to
                // obtain mutable access to the IPI area.
                let (handler, msg) =
                    deko_rwlock_write_atomic_data! {
                    PERCPU_AREAS,
                    cpu_areas,
                    cpu_areas_perm,
                    {
                        let Some(ref cpu_areas) = cpu_areas else {
                            die("PERCPU_AREAS is not initialized");
                        };

                        kpanic_if!(
                            core::hint::unlikely(i >= cpu_areas.0.len()),
                            "Target CPU ID",
                            i,
                            "exceeds current CPU count",
                            cpu_areas.0.len(),
                        );

                        let sender_cpu_shared = &cpu_areas.0[i].ipi_shared;
                        let tracked mut shared_perm_this = cpu_areas_perm.borrow_mut().shared_perms.tracked_remove(i as int);
                        // Now that the request has been handled, decrement the count of
                        // pending requests on the sender's bulletin board.  The IPI
                        // board may cease to be valid as soon as this decrement
                        // completes.
                        sender_cpu_shared.pending.fetch_sub_wrapping(Tracked(
                            &mut shared_perm_this.ipi_shared_perm.pending_perm
                        ), 1);

                        let msg = match sender_cpu_shared.message.borrow(Tracked(&shared_perm_this.ipi_shared_perm.message_perm)).as_ref() {
                            Some(e) => {
                                assume(e.wf());
                                Some(e.clone())
                            }
                            None => None,
                        };
                        let handler = sender_cpu_shared.handler.borrow(Tracked(&shared_perm_this.ipi_shared_perm.handler_perm)).clone();

                        proof {
                            cpu_areas_perm.borrow_mut().shared_perms.tracked_insert(i as int, shared_perm_this);
                        }

                        (handler, msg)
                    }
                };

                if let Some(msg) = msg {
                    unsafe {
                        make_ipi_handle_call(handler as usize, &msg);
                    }
                } else {
                    kwarn!("IPI message from CPU", i => hex, "is None, skipping...");
                }
            }
        }
    }
}

/// # Safety
///
/// The caller must ensure that `addr` is a valid function pointer (mapped).
#[inline]
#[verifier::external_body]
#[verus_spec(
    // with ???
    // requires???
)]
unsafe fn make_ipi_handle_call(addr: usize, arg: &DekoIpIMessage) {
    let f = core::mem::transmute::<usize, fn (DekoPPtr<DekoIpIMessage>)>(addr);

    f(DekoPPtr(vstd::simple_pptr::PPtr(arg as *const DekoIpIMessage as usize, PhantomData)));
}

/// This function handles the set affinity IPI message.
#[verus_spec(
    with
        Tracked(perm): Tracked<&DekoPointsTo<DekoIpIMessage>>,
    requires
        ptr@ == perm.pptr(),
        perm.is_init(),
        perm.wf(),
)]
pub fn handle_set_affinity(ptr: DekoPPtr<DekoIpIMessage>) {
    let msg = ptr.borrow(Tracked(&perm));

    match msg {
        DekoIpIMessage::AffinityChange { task } => {
            let (cpu, Tracked(cpu_perms)) = DekoCpuCtx::this_cpu();

            let rq = &cpu.borrow(Tracked(&cpu_perms.ptr_perm)).run_queue;
            kpanic_if!(
                core::hint::unlikely(rq.is_none()),
                "CPU has no run queue to set affinity task",
            );

            deko_rwlock_write_atomic_data! {
                rq.as_ref().unwrap(),
                rq,
                rq_perm,
                {
                    // Set this task to running.
                    deko_rwlock_write_atomic_data! {
                        &task.as_ref().data.state,
                        task_state,
                        __,
                        {
                            task_state.state = DekoRunnableState::RUNNING;
                        }
                    }

                    // Then enqueue it to the run queue.
                    #[verus_spec(with Tracked(rq_perm.borrow_mut()))]
                    rq.handle_task(task.clone());
                }
            }
        },
        _ => {
            kpanic_if!(
                true,
                "handle_set_affinity received non-affinity-change message",
            );
        },
    }
}

func_ptr!(handle_set_affinity);

#[verus_spec(
    with
        Tracked(perm): Tracked<&DekoPointsTo<DekoIpIMessage>>,
    requires
        ptr@ == perm.pptr(),
        perm.is_init(),
        perm.wf(),
)]
pub fn handle_tlb_shootdown(ptr: DekoPPtr<DekoIpIMessage>) {
    let msg = ptr.borrow(Tracked(&perm));

    kpanic_if!(
        core::hint::unlikely(!matches!(msg, DekoIpIMessage::TlbShootdown)),
        "handle_tlb_shootdown received non-TLB-shootdown message",
    );

    // Perform the TLB shootdown.
    flush_tlb_global_percpu();
}

func_ptr!(handle_tlb_shootdown);

} // verus!
