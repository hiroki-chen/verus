//! This is an extension to the Verus standard library that consists mainly of
//! various useful utilities and abstractions for system programming. This crate
//! provides the following modules:
//!
//! - `sync`: Provides synchronization primitives such as `Mutex`, `RwLock`, and `OnceCell`.
#![cfg_attr(not(test), no_std)]
#![allow(non_snake_case)]
#![allow(unused_imports)]
#![allow(unexpected_cfgs)]
#![allow(unused_macros)]
#![allow(non_shorthand_field_patterns)]
#![allow(mismatched_lifetime_syntaxes)]
#![cfg_attr(feature = "alloc", feature(allocator_api))]
#![feature(sized_hierarchy)]
#![feature(likely_unlikely)]

#[cfg(feature = "alloc")]
extern crate alloc;

extern crate self as deko_std;

use vstd::prelude::*;

#[cfg(feature = "alloc")]
pub mod boxed;

pub mod address;
pub mod array;
pub mod bits;
pub mod boot;
pub mod cpu;
pub mod fmt;
pub mod list;
pub mod math;
pub mod mem;
pub mod misc;
pub mod proofs;
pub mod ptr;
pub mod std_extra;
pub mod sync;
pub mod wf;

#[cfg(feature = "experimental")]
pub mod experimental;

#[cfg(feature = "snp")]
pub mod snp;

// Export everything.
pub mod prelude {
    pub use crate::address::*;
    pub use crate::array::*;
    pub use crate::bits::*;
    pub use crate::boot::*;
    #[cfg(feature = "alloc")]
    pub use crate::boxed::*;
    pub use crate::cpu::*;
    pub use crate::fmt::*;
    pub use crate::list::*;
    pub use crate::math::*;
    pub use crate::mem::*;
    pub use crate::misc::*;
    pub use crate::ptr::*;
    #[cfg(feature = "snp")]
    pub use crate::snp::*;
    pub use crate::std_extra::*;
    pub use crate::sync::*;
    pub use crate::wf::*;
    pub use crate::*;
}

verus! {

/// This is a globally accessible flag to indicate whether tracing (some debugging)
/// is enabled.
pub exec static TRACE_ON: DekoSimpleRwLock<bool> = DekoSimpleRwLock::new_simple(false);

#[verifier::external_body]
pub fn trace_enable(enabled: bool) {
    let (_, write_handle) = TRACE_ON.acquire_write();
    write_handle.release_write(DekoAtomicData::new(enabled));
}

#[verifier::external_body]
pub fn trace_is_enabled() -> bool {
    let read_handle = TRACE_ON.acquire_read();
    let enabled = read_handle.borrow().data;
    read_handle.release_read();

    enabled
}

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

impl<V: WellFormed> TrivialPredicate<V> {
    pub closed spec fn new() -> Self {
        TrivialPredicate(core::marker::PhantomData)
    }
}

impl<V: WellFormed> Predicate<V> for TrivialPredicate<V> {
    #[verifier::inline]
    open spec fn inv(self, __discard: V) -> bool {
        true
    }
}

impl<V: WellFormed> RwLockPredicate<V> for TrivialPredicate<V> {
    open spec fn inv(self, __discard: V) -> bool {
        true
    }
}

} // verus!
#[macro_export]
macro_rules! trace {
    ($($tt:tt)*) => {
        $crate::trace_enable(true);
        $($tt)*
        $crate::trace_enable(false);
    }
}
