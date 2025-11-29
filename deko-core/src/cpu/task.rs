use core::cmp::Ordering;

use deko_macros::DekoDebug;
use deko_std::cpu::no_irq_zone;
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use vstd::prelude::*;
use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl, PartialOrdSpecImpl};

verus! {

/// A `[DekoRunnable`]` represents a task that can be scheduled by the
/// task scheduler.
#[derive(DekoDebug)]
pub struct DekoRunnable {
    pub rsp: u64,
    /// The UUID of the task.
    pub uuid: [u8; 16],
    /// The priority of the task.
    pub priority: u8,
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
                // perform the actual context switch
                // ???
            },
    );
}

} // verus!
