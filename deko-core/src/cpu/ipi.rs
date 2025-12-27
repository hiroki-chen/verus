use core::ffi::c_void;
use core::marker::PhantomData;
use core::sync::atomic::AtomicU64;

use deko_macros::DekoDebug;
use deko_std::ptr::DekoPPtr;
use deko_std::sync::DekoAtomicData;
use deko_std::wf::WellFormed;
use deko_std::{deko_rwlock_write_atomic_data, with_permission};
use vstd::atomic::*;
use vstd::prelude::*;

use crate::cpu::apic::{Apic, X86Apic};
use crate::cpu::task::DekoRunnablePtr;
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission, PerCpuAreas, CPUID_MAX_COUNT, PERCPU_AREAS};
use crate::{die, kdebug, kpanic_if};

verus! {

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
    // pub request: (),
    pub message: DekoPPtr<DekoIpIMessage>,
    pub handler: DekoPPtr<u64>,  // extern "C" fn(*const msg),
}

impl CpuIpiArea {
    /// Creates a new and empty [`CpuIpiArea`].
    pub const fn new() -> (r: (Self, Tracked<CpuIpiAreaPermission>))
        ensures
            r.1@.pending_perm.is_for(r.0.pending),
            r.1@.request_set_perm.is_for(r.0.request_set),
            r.0.message.addr() == 0,
            r.0.handler.addr() == 0,
    {
        let (request_set, Tracked(request_set_perm)) = PAtomicU32::new(0);
        let (pending, Tracked(pending_perm)) = PAtomicUsize::new(0);

        (
            CpuIpiArea {
                request_set,
                pending,
                message: DekoPPtr(vstd::simple_pptr::PPtr(0usize, PhantomData)),
                handler: DekoPPtr(vstd::simple_pptr::PPtr(0usize, PhantomData)),
            },
            Tracked(CpuIpiAreaPermission { request_set_perm, pending_perm }),
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

/// Represents an Inter-Processor Interrupt (IPI) request.
#[derive(DekoDebug)]
pub struct DekoIpIRequest {
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

impl WellFormed for DekoIpIRequest {
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
impl DekoIpIRequest {
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

        DekoIpIRequest { targets: bitmap, message: msg, sender }
    }

    /// Sends the IPI to the target CPUs.
    #[verifier::exec_allows_no_decreases_clause]
    #[verus_spec(
        requires
            self.wf(),
    )]
    pub fn send_ipi(&self) {
        let (cpu, Tracked(cpu_perms)) = DekoCpuCtx::this_cpu();
        let id = cpu.borrow(Tracked(&cpu_perms.ptr_perm)).cpu_id as usize;
        let apic = &cpu.borrow(Tracked(&cpu_perms.ptr_perm)).apic;

        // kpanic_if!(
        //     (self.targets & (1 << id)) != 0,
        //     "CPU attempted to send IPI to itself:",
        //     id
        // );

        kpanic_if!(
            core::hint::unlikely(self.sender != id),
            "Sender ID mismatch: sender",
            id,
            "but recorded sender is ",
            self.sender,
        );

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
                send_ipi_to(i, apic);

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
                let ipi_area = &cpu_areas.0[id].ipi_shared;
                let tracked mut ipi_area_perm = cpu_areas_perm.borrow_mut().shared_perms.tracked_remove(id as int);

                // Increment the count of pending requests.
                ipi_area.pending.store(Tracked(&mut ipi_area_perm.ipi_shared_perm.pending_perm), cpu_nums as _);
                proof {
                    cpu_areas_perm.borrow_mut().shared_perms.tracked_insert(id as int, ipi_area_perm);
                }
            }
        );

        // Now let's wait for others to complete their handling.
        #[verus_spec(
            invariant
                self.wf(),
                0 <= id < CPUID_MAX_COUNT,
        )]
        loop {
            core::hint::spin_loop();

            deko_rwlock_write_atomic_data!(
                PERCPU_AREAS,
                cpu_areas,
                cpu_areas_perm,
                {
                    let tracked mut ipi_area_perm;
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
                    proof {
                        ipi_area_perm = cpu_areas_perm.borrow_mut().shared_perms.tracked_borrow(id as int);
                    }

                    let pending = ipi_area.pending.load(Tracked(&ipi_area_perm.ipi_shared_perm.pending_perm));

                    if pending == 0 {
                        break;
                    }
                }
            );
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

    let from_id = from.id();
    from.icr_write(low, high);

    deko_rwlock_write_atomic_data!(
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
            ipi_area.request_set.fetch_and(Tracked(&mut ipi_area_perm.ipi_shared_perm.request_set_perm), (1 << from.id()));

            proof {
                cpu_areas_perm.borrow_mut().shared_perms.tracked_insert(target as int, ipi_area_perm);
            }
        }
    );
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

        kdebug!("CPU", cpu_id => hex, "handling IPI request");

        // Need to check the IPI message and handle accordingly.
        // This write is just to obtain owned permissions to the IPI area.
        // So that we can reason about it.
        deko_rwlock_write_atomic_data! {
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


                let tracked mut ipi_area_perm;
                // Obtain a reference to this CPU's IPI area.
                let ipi_area = &cpu_areas.0[cpu_id].ipi_shared;
                proof {
                    ipi_area_perm = cpu_areas_perm.borrow_mut().shared_perms.tracked_borrow(cpu_id as int);
                }

                let cpu_set = ipi_area.request_set.load(Tracked(&ipi_area_perm.ipi_shared_perm.request_set_perm));

                // Enumerate over all CPUs
                for i in 0..cpu_areas.0.len()
                    invariant
                        0 <= i <= cpu_areas@.len() <= CPUID_MAX_COUNT,
                        cpu_areas.wf(),
                        cpu_areas@.len() == cpu_areas_perm@.shared_perms.len(),
                        forall|j: int|
                        #![trigger cpu_areas_perm@.shared_perms[j as int]]
                        0 <= j < cpu_areas@.len() as int ==> {
                            &&& cpu_areas@[j as int].wf()
                            &&& cpu_areas_perm@.shared_perms[j as int].online_perm.is_for(cpu_areas@[j as int].online)
                            &&& cpu_areas_perm@.shared_perms[j as int].ipi_pending_perm.is_for(cpu_areas@[j as int].ipi_pending)
                            &&& cpu_areas_perm@.shared_perms[j as int].nmi_pending_perm.is_for(cpu_areas@[j as int].nmi_pending)
                            &&& cpu_areas_perm@.shared_perms[j as int].ipi_irr_perm.len() == 8
                            &&& forall|k: int|
                                0 <= k < 8 ==> {
                                    #[trigger] cpu_areas_perm@.shared_perms[j as int].ipi_irr_perm[k as int].is_for(
                                        cpu_areas@[j as int].ipi_irr@[k as int],
                                    )
                                }
                            &&& cpu_areas_perm@.shared_perms[j as int].ipi_shared_perm.pending_perm.is_for(
                                cpu_areas@[j as int].ipi_shared.pending,
                            )
                            &&& cpu_areas_perm@.shared_perms[j as int].ipi_shared_perm.request_set_perm.is_for(
                                cpu_areas@[j as int].ipi_shared.request_set,
                            )
                        }
                {
                    if (cpu_set & (1 << i)) != 0 {
                        kdebug!("CPU", cpu_id => hex, "handling IPI from CPU", i => hex);
                        // Handle the IPI from CPU i.
                        let cpu_shared_this = &cpu_areas.0[i].ipi_shared;
                        let tracked mut shared_perm_this = cpu_areas_perm.borrow_mut().shared_perms.tracked_remove(i as int);

                        unsafe {
                            #[verus_spec(with Tracked(&mut shared_perm_this.ipi_shared_perm))]
                            receive_single_ipi(&cpu_shared_this);
                        }

                        // Now that the request has been handled, decrement the count of
                        // pending requests on the sender's bulletin board.  The IPI
                        // board may cease to be valid as soon as this decrement
                        // completes.
                        cpu_shared_this.pending.fetch_sub_wrapping(Tracked(
                            &mut shared_perm_this.ipi_shared_perm.pending_perm
                        ), 1);

                        proof {
                            cpu_areas_perm.borrow_mut().shared_perms.tracked_insert(i as int, shared_perm_this);
                        }
                    }
                }
            }
        };

        kdebug!("CPU", cpu_id => hex, "completed IPI handling");
    }
}

/// Receives a single IPI and invoke the handler to handle this IPI.
///
/// The caller must ensure that the message and the handler is valid
/// and mapped in memory.
#[inline]
#[verus_spec(
    with
        Tracked(ipi_area_perm): Tracked<&mut CpuIpiAreaPermission>,
    requires
        old(ipi_area_perm).pending_perm.is_for(ipi_area.pending),
        old(ipi_area_perm).request_set_perm.is_for(ipi_area.request_set),
    ensures
        ipi_area_perm.pending_perm.is_for(ipi_area.pending),
        ipi_area_perm.request_set_perm.is_for(ipi_area.request_set),
        old(ipi_area_perm).pending_perm.value() == ipi_area_perm.pending_perm.value(),
)]
unsafe fn receive_single_ipi(ipi_area: &CpuIpiArea) {
    // stub for now.
    let handler_ptr = ipi_area.handler.addr();

    // TODO: Need to check if the pointer is valid; but how??
    make_ipi_handle_call(handler_ptr, ipi_area.message);
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
unsafe fn make_ipi_handle_call(addr: usize, arg: DekoPPtr<DekoIpIMessage>) {
    let f = core::mem::transmute::<usize, extern "C" fn (DekoPPtr<DekoIpIMessage>)>(addr);

    f(arg);
}

} // verus!
