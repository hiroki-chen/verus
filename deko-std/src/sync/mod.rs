#[cfg(feature = "alloc")]
pub mod arc;

pub mod lazy;
pub mod mutex;
pub mod once;
pub mod rwlock;

use vstd::prelude::*;

verus! {

/// A wrapper around the actual data held by any runtime-checked synchronization primitive
///
/// This allows us to reason about the permissioned data stored in the lock.
pub struct DekoAtomicData<V, P> {
    pub data: V,
    pub perm: Tracked<P>,
}

impl<V: WellFormed, P> WellFormed for DekoAtomicData<V, P> {
    open spec fn wf(&self) -> bool {
        self.data.wf()
    }
}

pub spec const ATOMIC_CELL_ID: int = 0x114514;

pub spec const ARC_ID: int = 0x1919810;

pub const UNINIT: u64 = 0;

pub const OCCUPIED: u64 = 1;

pub const INITED: u64 = 2;

} // verus!
#[cfg(feature = "alloc")]
pub use arc::*;
pub use lazy::*;
pub use mutex::*;
pub use once::*;
pub use rwlock::*;

use crate::WellFormed;
