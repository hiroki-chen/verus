#![no_std]
#![feature(proc_macro_hygiene)]
#![feature(abi_x86_interrupt)]
#![feature(allocator_api)]
#![feature(core_intrinsics)]
#![feature(never_type)]
#![feature(trait_alias)]
#![allow(named_asm_labels)]
#![allow(binary_asm_labels)]

use deko_std::prelude::*;
use elf::ElfFile;
use vstd::prelude::*;

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

verus! {

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

/// This piece of information is provided by IGVM to stage2 so we do not
/// explicitly construct it.
///
/// The parameter's structure is defined in svsm/igvmbuilder; we can also
/// construct one on our own if needed but not necessary for the time being.
#[repr(C, packed)]
#[derive(Clone, Copy)]
pub struct Stage2LaunchInfo {
    // VTOM must be the first field.
    pub vtom: u64,
    // platform_type must be the second field.
    pub platform_type: u32,
    // cpuid_page must be the third field.
    pub cpuid_page: u32,
    // secrets_page must be the fourth field.
    pub secrets_page: u32,
    pub stage2_end: u32,
    pub kernel_elf_start: u32,
    pub kernel_elf_end: u32,
    pub kernel_fs_start: u32,
    pub kernel_fs_end: u32,
    pub igvm_params: u32,
    pub _reserved: u32,
}

impl Stage2LaunchInfo {
    pub uninterp spec fn get_igvm_params_spec(&self) -> IgvmParamBlock;
}

impl WellFormed for Stage2LaunchInfo {
    // FIXME: There are some self-contradictory definitions here.
    open spec fn wf(&self) -> bool {
        // The Stage2LaunchInfo is well-formed if the addresses are aligned.
        &&& self.vtom % 0x1000 == 0
        &&& self.cpuid_page % 0x1000 == 0
        &&& self.cpuid_page != 0
        &&& self.secrets_page % 0x1000 == 0
        &&& self.secrets_page != 0
        &&& self.stage2_end % 0x1000 == 0
        &&& self.kernel_elf_start % 0x1000 == 0
        &&& self.kernel_elf_end % 0x1000 == 0
        &&& self.kernel_elf_start <= self.kernel_elf_end <= u32::MAX
        &&& self.platform_type == 0x0001 || self.platform_type == 0x0002
        &&& self.platform_type matches 0x0001 ==> self.vtom != 0
        &&& self.stage2_end > STAGE2_START
        &&& self.stage2_end <= u32::MAX  // ensures no overflow.
        &&& self.get_igvm_params_spec().find_kernel_region_spec() matches Some((kstart, kend)) ==> {
            ElfFile::new_spec(
                PhysAddr(self.kernel_elf_start as u64),
                PhysAddr(self.kernel_elf_end as u64),
            ) matches Some(elf_file) ==> elf_file.wf_with_load_base(kstart)
        }
    }
}

} // verus!
