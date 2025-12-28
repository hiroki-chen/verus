//! Verified synchronization primitives for low-level OS programming.
//!
//! This module provides several synchronization primitives that are
//! suitable for use in low-level operating system code, including:
//!
//! - [`mutex::Mutex`]: A mutual exclusion lock for protecting shared data.
//! - [`rwlock::RwLock`]: A reader-writer lock for allowing concurrent read access.
//! - [`once::OnceCell`]: A cell that can be initialized exactly once.
//! - [`arc::Arc`]: An atomically reference-counted pointer for shared ownership.
//! - [`lazy::Lazy`]: A lazily initialized value.
//! - [`atomic::AtomicPtr`]: An atomic pointer type for safe concurrent access.
//!
//! Each primitive is designed to be thread-safe and can be used in static
//! contexts. They leverage Verus's verification capabilities to ensure
//! correctness properties about concurrent access and data integrity.
//!
//! # Important notes
//!
//! The current version of these synchronization primitives does not guarantee
//! safety and liveness properties (e.g., no deadlocks, and locks are eventually
//! acquired if attempted) due to the limitation of VerusSync.
//!
//! In the future, this module might be migrated to TLA+ based reasoning system
//! supported by Anvil.
#[cfg(feature = "alloc")]
pub mod arc;
pub mod atomic;
pub mod lazy;
pub mod mutex;
pub mod once;
pub mod rwlock;

#[cfg(feature = "alloc")]
pub use arc::*;
use deko_macros::DekoDebug;
pub use lazy::*;
pub use mutex::*;
pub use once::*;
pub use rwlock::*;
use vstd::prelude::*;
use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};
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

impl<T: WellFormed, P> View for DekoAtomicData<T, P> {
    type V = T;

    open spec fn view(&self) -> T {
        self.data
    }
}

impl<V: crate::fmt::DekoDebug, P> crate::fmt::DekoDebug for DekoAtomicData<V, P> {
    #[verifier::external_body]
    fn deko_debug<W: deko_std::prelude::DekoWriter>(&self, writer: &W) {
        writer.write_str("DekoAtomicData{ data: ");
        self.data.deko_debug(writer);
        writer.write_str(" }");
    }
}

impl<V: WellFormed + PartialEq + PartialEqSpec, P> PartialEqSpecImpl for DekoAtomicData<V, P> {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        <V as PartialEqSpec>::eq_spec(&self.data, &other.data)
    }
}

impl<V: WellFormed + PartialEq, P> PartialEq for DekoAtomicData<V, P> {
    #[inline]
    #[verifier::external_body]
    fn eq(&self, other: &Self) -> bool {
        <V as PartialEq>::eq(&self.data, &other.data)
    }
}

pub spec const ATOMIC_CELL_ID: int = 0x114514;

pub spec const ARC_ID: int = 0x1919810;

pub const UNINIT: u64 = 0;

pub const OCCUPIED: u64 = 1;

pub const INITED: u64 = 2;

} // verus!
