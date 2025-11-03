#![no_std]
#![feature(proc_macro_hygiene)]
#![feature(abi_x86_interrupt)]
#![feature(allocator_api)]
#![feature(never_type)]
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
