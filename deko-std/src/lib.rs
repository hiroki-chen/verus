//! This is an extension to the Verus standard library that consists mainly of
//! various useful utilities and abstractions for system programming. This crate
//! provides the following modules:
//!
//! - `sync`: Provides synchronization primitives such as `Mutex`, `RwLock`, and `OnceCell`.
#![no_std]
#![allow(non_snake_case)]
#![allow(unused_imports)]
#![allow(unexpected_cfgs)]
#![cfg_attr(feature = "alloc", feature(allocator_api))]

#[cfg(feature = "alloc")]
pub mod boxed;

pub mod bits;
pub mod boot;
pub mod cpu;
pub mod mem;
pub mod misc;
pub mod proofs;
pub mod ptr;
pub mod sync;
pub mod wf;

// Export everything.
pub mod prelude {
    pub use crate::bits::*;
    pub use crate::boot::*;
    pub use crate::cpu::*;
    pub use crate::mem::*;
    pub use crate::misc::*;
    pub use crate::ptr::*;
    pub use crate::sync::*;
    pub use crate::wf::*;
}
