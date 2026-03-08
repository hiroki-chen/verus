use deko_std::sync::{DekoAtomicData, RwLock, Spin};
use deko_std::wf::WellFormed;
use deko_std::with_permission;
use vstd::atomic::{PAtomicBool, PAtomicI32, PermissionBool, PermissionI32};
use vstd::prelude::*;

use crate::cpu::DekoCpuCtx;
use crate::snp::is_vmpl1;
use crate::{kinfo, kpanic_if};

verus! {

pub type DekoUnsafeRwLock<V, P, Pred> = RwLock<DekoAtomicData<V, P>, IrqUnSafeLockGuard, Pred>;

pub type DekoSafeRwLock<V, P, Pred> = RwLock<DekoAtomicData<V, P>, IrqSafeLockGuard, Pred>;

/// A spinlock that does not disable interrupts. This is only safe to use
/// in contexts where interrupts are already disabled.
pub struct IrqUnSafeLockGuard;

pub struct IrqSafeLockGuard;

#[verifier::external]
impl Spin for IrqSafeLockGuard {
    type GuardData = ();

    // rflags.
    #[inline]
    fn lock_prologue() -> Self::GuardData {
        irq_disable();
    }

    fn cpu_relax() {
        core::hint::spin_loop();
    }

    #[inline]
    fn lock_epilogue(data: &Self::GuardData) {
        irq_enable();
    }
}

#[verifier::external]
impl Spin for IrqUnSafeLockGuard {
    type GuardData = ();

    // rflags.
    #[inline]
    fn lock_prologue() -> Self::GuardData {
        ()
    }

    fn cpu_relax() {
        core::hint::spin_loop();
    }

    #[inline]
    fn lock_epilogue(data: &Self::GuardData) {
    }
}

/// This structure keeps track of PerCpu IRQ states. It tracks the original IRQ
/// state and how deep IRQ-disable calls have been nested. The use of atomics
/// is necessary for interior mutability and to make state modifications safe
/// wrt. to IRQs.
///
/// The original state needs to be stored to not accidentially enable IRQs in
/// contexts which have IRQs disabled by other means, e.g. in an exception or
/// NMI/HV context.
pub struct IrqState {
    /// IRQ state when count was `0`.
    pub state: PAtomicBool,
    /// Depth of IRQ-disabled nesting.  Index 0 specifies the count of
    /// IRQ disables and the remaining indices specify the nesting count
    /// for eached raised TPR level.
    pub counts: [PAtomicI32; 0x10],
}

impl WellFormed for IrqState {
    open spec fn wf(&self) -> bool {
        true
    }
}

#[verus_verify]
impl IrqState {
    /// Push a new IRQ-disable request onto the stack.
    #[verus_spec(
        with
            Tracked(perm): Tracked<&mut IrqStatePermission>,
        requires
            old(perm).wf_with(old(self)),
        ensures
            perm.wf_with(self),
    )]
    pub fn push(&mut self, was_enabled: bool) {
        // todo: add this for both VMPL0 and VMPL1.
        let tracked mut count0_perm = perm.counts_perm.tracked_remove(0);

        let val = self.counts[0].fetch_add_wrapping(Tracked(&mut count0_perm), 1);
        if val == 0 {
            self.state.store(Tracked(&mut perm.state_perm), was_enabled);
        }
        proof {
            perm.counts_perm.tracked_insert(0, count0_perm);
        }
    }

    /// Decrease IRQ-disable nesting level by 1.
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut IrqStatePermission>,
        requires
            old(perm).wf_with(old(self)),
        ensures
            perm.wf_with(self),
    )]
    pub fn pop(&mut self) -> i32 {
        let tracked mut count0_perm = perm.counts_perm.tracked_remove(0);
        let val = self.counts[0].fetch_sub_wrapping(Tracked(&mut count0_perm), 1);
        proof {
            perm.counts_perm.tracked_insert(0, count0_perm);
        }

        val.wrapping_sub(1)
    }
}

with_permission!(
    IrqState,
    state_perm: PermissionBool,
    counts_perm: Seq<PermissionI32>,
);

impl IrqStatePermission {
    pub open spec fn wf_with(&self, irq_state: &IrqState) -> bool {
        &&& self.state_perm.is_for(irq_state.state)
        &&& forall|i: int|
            #![trigger self.counts_perm[i]]
            0 <= i && i < 0x10 ==> self.counts_perm[i].is_for(irq_state.counts@[i])
        &&& self.counts_perm.len() == irq_state.counts@.len() == 0x10
    }
}

impl IrqState {
    /// Create a new IrqState with all counts set to zero and IRQs enabled.
    pub const fn new() -> (r: (Self, Tracked<IrqStatePermission>))
        ensures
            r.0.wf(),
            r.1@.wf_with(&r.0),
    {
        let (arr, perms) =
            seq_macro::seq! {
            N in 0..16 {{
                #(
                    let (atomic~N, perm~N) = PAtomicI32::new(0);
                )*

                let arr = [
                    #( atomic~N, )*
                ];

                let perms = [
                    #( perm~N, )*
                ];

                (arr, perms)
            }}
        };

        let (state, Tracked(state_perm)) = PAtomicBool::new(false);
        let tracked perms_transformed = Seq::tracked_new(0x10, |i| perms@[i as int]@);

        (
            IrqState { state, counts: arr },
            Tracked(IrqStatePermission { state_perm, counts_perm: perms_transformed }),
        )
    }
}

#[inline]
#[verifier::external_body]
pub fn raw_irq_disable() {
    unsafe {
        core::arch::asm!(
            "cli",
            options(att_syntax, nostack, nomem)
        );
    }
}

#[inline]
#[verifier::external_body]
pub fn raw_irq_enable() {
    unsafe {
        core::arch::asm!("sti", options(att_syntax, nostack, nomem));
    }
}

#[verus_spec(r =>
    // with
        // Tracked(core): Tracked<DekoCPUCore>,
)]
fn irq_disable_vmpl0(irq_enabled: bool) {
    // First we need to push to the cpu.
    let (this_cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let mut cpu_taken = this_cpu.take(Tracked(&mut cpu_perm.ptr_perm));

    proof_with!(Tracked(&mut cpu_perm.irq_state_perm));
    cpu_taken.nested_irq.push(irq_enabled);

    // Finally, put back the cpu.
    this_cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);
}

#[verus_spec(r =>
        // with
        // Tracked(core): Tracked<DekoCPUCore>,
)]
fn irq_disable_vmpl1(irq_enabled: bool) {
    let (this_cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();

    let mut cpu_taken = this_cpu.take(Tracked(&mut cpu_perm.ptr_perm));
    let ext_vmpl1 = cpu_taken.ext_vmpl1.take();
    kpanic_if!(core::hint::unlikely(ext_vmpl1.is_none()), "VMPL1 CPU context not initialized");

    let tracked mut ext_vmpl1_perm = cpu_perm.ext_vmpl1_perm.tracked_take();
    let mut ext_vmpl1 = ext_vmpl1.unwrap();

    proof_with!(Tracked(&mut ext_vmpl1_perm.nested_irq_perm));
    ext_vmpl1.nested_irq.push(irq_enabled);

    // Put back the VMPL1 context.
    cpu_taken.ext_vmpl1.replace(ext_vmpl1);
    proof {
        cpu_perm.ext_vmpl1_perm = Some(ext_vmpl1_perm);
    }
    this_cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);
}

/// Disable the CPU interrupts.
#[inline]
#[verus_spec(r =>
        // with
        // Tracked(core): Tracked<DekoCPUCore>,
)]
pub fn irq_disable() {
    // Now disable the IRQs.
    let irq_enabled = irq_enabled();
    raw_irq_disable();

    if !is_vmpl1() {
        irq_disable_vmpl0(irq_enabled);
    } else {
        irq_disable_vmpl1(irq_enabled);
    }
}

#[verus_spec(r =>
    // with
        // Tracked(core): Tracked<DekoCPUCore>,
)]
#[verifier::exec_allows_no_decreases_clause]
fn irq_enable_vmpl0() {
    let (this_cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let mut cpu_taken = this_cpu.take(Tracked(&mut cpu_perm.ptr_perm));
    let mut should_enable = false;

    proof_with!(Tracked(&mut cpu_perm.irq_state_perm));
    let val = cpu_taken.nested_irq.pop();
    kpanic_if!(core::hint::unlikely(val < 0), "irq_enable_vmpl0 underflow");

    if val == 0 {
        let state = cpu_taken.nested_irq.state.load(
            Tracked(&mut cpu_perm.irq_state_perm.state_perm),
        );

        if state {
            should_enable = true;
        }
    }
    this_cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);

    if should_enable {
        crate::imp::after_irq_enable();
        raw_irq_enable();
    }
}

#[verus_spec(r =>
    // with
        // Tracked(core): Tracked<DekoCPUCore>,
)]
#[verifier::exec_allows_no_decreases_clause]
fn irq_enable_vmpl1() {
    let (this_cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let mut should_enable = false;

    let mut cpu_taken = this_cpu.take(Tracked(&mut cpu_perm.ptr_perm));
    let ext_vmpl1 = cpu_taken.ext_vmpl1.take();
    kpanic_if!(core::hint::unlikely(ext_vmpl1.is_none()), "VMPL1 CPU context not initialized");

    let tracked mut ext_vmpl1_perm = cpu_perm.ext_vmpl1_perm.tracked_take();
    let mut ext_vmpl1 = ext_vmpl1.unwrap();

    proof_with!(Tracked(&mut ext_vmpl1_perm.nested_irq_perm));
    let val = ext_vmpl1.nested_irq.pop();
    kpanic_if!(core::hint::unlikely(val < 0), "irq_enable_vmpl1 underflow");

    if val == 0 {
        let state = ext_vmpl1.nested_irq.state.load(
            Tracked(&mut ext_vmpl1_perm.nested_irq_perm.state_perm),
        );

        if state {
            should_enable = true;
        }
    }
    // Put back the VMPL1 context.

    cpu_taken.ext_vmpl1.replace(ext_vmpl1);
    proof {
        cpu_perm.ext_vmpl1_perm = Some(ext_vmpl1_perm);
    }
    this_cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);

    if should_enable {
        crate::imp::after_irq_enable();
        raw_irq_enable();
    }
}

/// Enable the CPU interrupts.
#[verus_spec(r =>
    // with
        // Tracked(core): Tracked<DekoCPUCore>,
)]
#[verifier::exec_allows_no_decreases_clause]
pub fn irq_enable() {
    if is_vmpl1() {
        irq_enable_vmpl1();
    } else {
        irq_enable_vmpl0();
    }
}

#[inline]
#[verifier::external_body]
pub fn rflags() -> u64 {
    let rflags: u64;
    unsafe {
        core::arch::asm!(
            "pushfq",
            "popq {}",
            out(reg) rflags,
            options(att_syntax)
        );
    }

    rflags
}

/// Check if the the CPU interrupts are enabled.
#[inline]
#[verifier::external_body]
#[verus_spec(r =>
    // with
        // Tracked(core): Tracked<DekoCPUCore>,
)]
pub fn irq_enabled() -> bool {
    let rflags = rflags();

    (rflags & (1 << 9)) == (1 << 9)
}

/// Enter a zone where interrupts are disabled.
#[verifier::external_body]
pub fn no_irq_zone<T>(f: impl FnOnce() -> T) -> T {
    irq_disable();

    let v = f();

    irq_enable();

    v
}

#[verifier::exec_allows_no_decreases_clause]
pub fn log_nested_irq_state(marker: u64) {
    let cur_vmpl1 = is_vmpl1();
    let if_enabled = irq_enabled();

    let (this_cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let mut cpu_taken = this_cpu.take(Tracked(&mut cpu_perm.ptr_perm));

    // VMPL0 irq state
    let vmpl0_count;
    proof_with!(Tracked(&mut cpu_perm.irq_state_perm));
    let tracked mut vmpl0_count_perm = cpu_perm.irq_state_perm.counts_perm.tracked_remove(0);
    vmpl0_count = cpu_taken.nested_irq.counts[0].load(Tracked(&mut vmpl0_count_perm));
    proof {
        cpu_perm.irq_state_perm.counts_perm.tracked_insert(0, vmpl0_count_perm);
    }
    let vmpl0_state = cpu_taken.nested_irq.state.load(
        Tracked(&mut cpu_perm.irq_state_perm.state_perm),
    );

    // VMPL1 irq state
    let mut vmpl1_present = false;
    let mut vmpl1_count: i32 = -1;
    let mut vmpl1_state = false;
    if let Some(ext_vmpl1) = cpu_taken.ext_vmpl1.take() {
        vmpl1_present = true;
        let mut ext_vmpl1 = ext_vmpl1;
        let tracked mut ext_vmpl1_perm = cpu_perm.ext_vmpl1_perm.tracked_take();

        proof_with!(Tracked(&mut ext_vmpl1_perm.nested_irq_perm));
        let tracked mut vmpl1_count_perm =
            ext_vmpl1_perm.nested_irq_perm.counts_perm.tracked_remove(0);
        vmpl1_count = ext_vmpl1.nested_irq.counts[0].load(Tracked(&mut vmpl1_count_perm));
        proof {
            ext_vmpl1_perm.nested_irq_perm.counts_perm.tracked_insert(0, vmpl1_count_perm);
        }
        vmpl1_state =
        ext_vmpl1.nested_irq.state.load(Tracked(&mut ext_vmpl1_perm.nested_irq_perm.state_perm));

        cpu_taken.ext_vmpl1.replace(ext_vmpl1);
        proof {
            cpu_perm.ext_vmpl1_perm = Some(ext_vmpl1_perm);
        }
    }
    this_cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);

    kinfo!(
        "nested_irq_state",
        "marker", marker => hex,
        "cur_vmpl", if cur_vmpl1 { 1 } else { 0 },
        "if", if if_enabled { 1 } else { 0 },
        "vmpl0_count", vmpl0_count as i64,
        "vmpl0_state", if vmpl0_state { 1 } else { 0 },
        "vmpl1_present", if vmpl1_present { 1 } else { 0 },
        "vmpl1_count", vmpl1_count as i64,
        "vmpl1_state", if vmpl1_state { 1 } else { 0 }
    );
}

} // verus!
