//! This is an extension to the Verus standard library that consists mainly of
//! various useful utilities and abstractions for system programming. This crate
//! provides the following modules:
//!
//! - `sync`: Provides synchronization primitives such as `Mutex`, `RwLock`, and `OnceCell`.
#![cfg_attr(not(test), no_std)]
#![allow(non_snake_case)]
#![allow(unused_imports)]
#![allow(unexpected_cfgs)]
#![cfg_attr(feature = "alloc", feature(allocator_api))]

use vstd::prelude::*;

#[cfg(feature = "alloc")]
pub mod boxed;

pub mod array;
pub mod bits;
pub mod boot;
pub mod cpu;
pub mod list;
pub mod math;
pub mod mem;
pub mod misc;
pub mod proofs;
pub mod ptr;
pub mod sync;
pub mod wf;

// Export everything.
pub mod prelude {
    pub use crate::array::*;
    pub use crate::bits::*;
    pub use crate::boot::*;
    #[cfg(feature = "alloc")]
    pub use crate::boxed::*;
    pub use crate::cpu::*;
    pub use crate::list::*;
    pub use crate::math::*;
    pub use crate::mem::*;
    pub use crate::misc::*;
    pub use crate::ptr::*;
    pub use crate::sync::*;
    pub use crate::wf::*;
    pub use crate::*;
}

verus! {

use crate::prelude::*;

pub trait Predicate<V>: Sized {
    spec fn inv(self, v: V) -> bool;
}

// Dummy implementation if we don't care about the predicate.
impl<V> Predicate<V> for () {
    #[verifier::inline]
    open spec fn inv(self, __discard: V) -> bool {
        true
    }
}

/// A helper predicate that always returns true for any value of type `V`.
/// This is used when there is no predicate on the value should be used.
pub struct TrivialPredicate<V: WellFormed>(core::marker::PhantomData<V>);

impl<V: WellFormed> Predicate<V> for TrivialPredicate<V> {
    #[verifier::inline]
    open spec fn inv(self, __discard: V) -> bool {
        true
    }
}

// == Type alias for trivial types that do not require any predicate. ==
#[cfg(feature = "alloc")]
pub type BoxNoPred<V> = Box<V, TrivialPredicate<V>>;

// #[cfg(feature = "alloc")]
// pub type ArcNoPred<V> = Arc<V, TrivialPredicate<V>>;
pub type MutexNoPred<V> = Mutex<V, TrivialPredicate<V>>;

pub type OnceLockNoPred<V> = OnceLock<V, TrivialPredicate<V>>;

pub type RwLockNoPred<V> = RwLock<V, TrivialPredicate<V>>;

} // verus!
