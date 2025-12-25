use deko_macros::DekoDebug;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::cpu::apic::{Apic, X86Apic};
use crate::cpu::task::DekoRunnablePtr;
use crate::cpu::{DekoCpuCtx, CPUID_MAX_COUNT, PERCPU_AREAS};
use crate::{kdebug, kpanic_if};

verus! {

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
        for i in 0..CPUID_MAX_COUNT
            invariant
                0 <= i <= CPUID_MAX_COUNT,
                self.wf(),
        {
            if (self.targets & (1 << i)) != 0 {
                send_ipi_to(i, apic);
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

    from.icr_write(low, high);
}

} // verus!
