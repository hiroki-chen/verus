use core::sync::atomic::AtomicU64;

use vstd::prelude::*;

use crate::cell::UnsafeCell;

verus! {

#[verifier::external_body]
pub struct Spin {
    current: AtomicU64,
    holder: AtomicU64,
}

impl Spin {
    pub uninterp spec fn id(self) -> int;

    #[verifier::external_body]
    pub const fn new() -> (ret: Self) {
        Self { current: AtomicU64::new(1), holder: AtomicU64::new(1) }
    }

    pub open spec fn is_locked(&self) -> bool {
        true
    }
}

/// A spinlock that can be used to protect shared data in the monitor.
///
/// This is backed by a spin lock to ensure atomicity.
#[verifier::reject_recursive_types(T)]
#[verifier::external_body]
pub struct Mutex<T> {
    spin: Spin,
    data: UnsafeCell<T>,
}

} // verus!
