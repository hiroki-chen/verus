#[cfg(feature = "alloc")]
pub mod arc;
pub mod atomic;
pub mod lazy;
pub mod mutex;
pub mod once;
pub mod rwlock;

#[cfg(feature = "alloc")]
pub use arc::*;
pub use lazy::*;
pub use mutex::*;
pub use once::*;
pub use rwlock::*;
use vstd::prelude::*;
use vstd::std_specs::convert::FromSpecImpl;

use crate::std_extra::convert::AsRefSpecImpl;
use crate::WellFormed;

verus! {

pub type DekoAtomicDataNoPerm<V> = DekoAtomicData<V, ()>;

/// A wrapper around the actual data held by any runtime-checked synchronization
/// primitive which allows us to reason about the permissioned data stored in the
/// lock. The caller is responsible for providing a tracked permission type `P` that
/// corresponds to the data `V`, e.g., a [`vstd::simple_pptr::PointsTo<V>`] so that
/// some high-level properties can be verified about the data stored in the lock.
pub struct DekoAtomicData<V, P> {
    pub data: V,
    pub perm: Tracked<P>,
}

impl<V, P> DekoAtomicData<V, P> {
    /// Creates a new [`DekoAtomicData`] wrapping the given data and permission.
    pub const fn new_with(data: V, perm: Tracked<P>) -> (r: Self)
        returns
            (Self { data, perm }),
    {
        DekoAtomicData { data, perm }
    }
}

impl<V> DekoAtomicDataNoPerm<V> {
    /// Creates a new [`DekoAtomicData`] wrapping the given data with no permission.
    pub const fn new(data: V) -> (r: Self)
        ensures
            r.data == data,
    {
        let perm = Tracked(());
        DekoAtomicData { data, perm }
    }
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
