#![no_std]
#![feature(proc_macro_hygiene)]
#![feature(abi_x86_interrupt)]
#![feature(allocator_api)]
#![feature(core_intrinsics)]
#![feature(never_type)]
#![feature(trait_alias)]
#![allow(named_asm_labels)]
#![allow(binary_asm_labels)]

#[cfg(not(target_arch = "x86_64"))]
compile_error!("Cannot be compiled against non x86_64 architecture!");

#[cfg(all(feature = "tdx", feature = "snp"))]
compile_error!("Cannot enable both TDX and SEV features at the same time!");

pub mod allocator;
pub mod boot;
pub mod cpu;
pub mod elf;
pub mod hal;
pub mod imp;
pub mod logging;
pub mod mm;
pub mod policy;

// TODO: Split our crate into three parts.
pub mod exec;
pub mod proof;
pub mod spec;

#[cfg(feature = "snp")]
pub mod snp;
#[cfg(feature = "tdx")]
pub mod tdx;

/// We avoid using [`vstd::vpanic`] to prevent heap-allocated strings
/// that panics itself:
///
/// ```rust
/// // rt::Argument is a private type and we cannot add specification directly
/// #[cfg(feature = "alloc")]
// #[doc(hidden)]
/// #[verifier(external_body)]
/// pub fn __new_argument<T: core::fmt::Debug>(v: &T) -> alloc::string::String {
///     alloc::format!("{:?}", v)
/// }
/// ```
#[track_caller]
#[inline(always)]
#[verifier::external_body]
pub fn die(s: &str) -> ! {
    core::panic!("{}", s);
}
