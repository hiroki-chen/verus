//! Synchronization primitives for the deko monitor.
pub mod mutex;

use vstd::prelude::*;

verus! {

pub ghost struct LockPerm {
    pub locked: bool,
    pub cpu_id: nat,
    pub data: (),
}

} // verus!
