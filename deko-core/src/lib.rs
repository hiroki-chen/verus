#![no_std]
#![feature(proc_macro_hygiene)]
#![feature(abi_x86_interrupt)]
#![feature(allocator_api)]
#![feature(core_intrinsics)]
#![feature(never_type)]
#![feature(trait_alias)]
#![allow(named_asm_labels)]
#![allow(binary_asm_labels)]
#![allow(mismatched_lifetime_syntaxes)]

#[cfg(feature = "alloc")]
extern crate alloc;

use deko_macros::DekoDebug;
use deko_std::prelude::*;
use elf::ElfFile;
use vstd::prelude::*;

#[cfg(not(target_arch = "x86_64"))]
compile_error!("Cannot be compiled against non x86_64 architecture!");

#[cfg(all(feature = "tdx", feature = "snp"))]
compile_error!("Cannot enable both TDX and SEV features at the same time!");

pub mod boot;
#[cfg(feature = "alloc")]
pub mod collections;
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
#[derive(Clone, Copy, DekoDebug)]
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
    #[deko(skip)]
    pub _reserved: u32,
}

#[derive(Copy, Clone, DekoDebug)]
#[repr(C)]
pub struct DekoKernelLaunchInfo {
    /// Start of the kernel in physical memory.
    #[deko(hex)]
    pub kernel_region_phys_start: u64,
    /// Exclusive end of the kernel in physical memory.
    #[deko(hex)]
    pub kernel_region_phys_end: u64,
    #[deko(hex)]
    pub heap_area_phys_start: u64,  // Start of trailing heap area within the physical memory region.
    #[deko(hex)]
    pub heap_area_size: u64,
    #[deko(hex)]
    pub kernel_region_virt_start: u64,
    #[deko(hex)]
    pub heap_area_virt_start: u64,  // Start of virtual heap area mapping.
    #[deko(hex)]
    pub kernel_elf_stage2_virt_start: u64,  // Virtual address of kernel ELF in Stage2 mapping.
    #[deko(hex)]
    pub kernel_elf_stage2_virt_end: u64,
    #[deko(hex)]
    pub kernel_fs_start: u64,
    #[deko(hex)]
    pub kernel_fs_end: u64,
    #[deko(hex)]
    pub stage2_start: u64,
    #[deko(hex)]
    pub stage2_end: u64,
    #[deko(hex)]
    pub cpuid_page: u64,
    #[deko(hex)]
    pub secrets_page: u64,
    #[deko(hex)]
    pub stage2_igvm_params_phys_addr: u64,
    #[deko(hex)]
    pub stage2_igvm_params_size: u64,
    #[deko(hex)]
    pub igvm_params_phys_addr: u64,
    #[deko(hex)]
    pub igvm_params_virt_addr: u64,
    #[deko(hex)]
    pub vtom: u64,
    #[deko(hex)]
    pub debug_serial_port: u16,
    pub use_alternate_injection: bool,
    #[deko(enabled)]
    pub suppress_deko_interrupts: bool,
}

impl Stage2LaunchInfo {
    pub uninterp spec fn get_igvm_param_block_spec(&self) -> IgvmParamBlock;

    pub uninterp spec fn get_igvm_params_spec<>(&self) -> IgvmParams<'_>;

    pub open spec fn get_elf(&self) -> Option<ElfFile> {
        if self.get_igvm_param_block_spec().find_kernel_region_spec() matches Some((kstart, kend)) {
            ElfFile::new_spec(self.kernel_elf_start as u64, self.kernel_elf_end as u64)
        } else {
            None
        }
    }

    pub open spec fn wf_for_loading(&self, ms: MappingSpace) -> bool {
        &&& self.wf()
        &&& self.get_igvm_param_block_spec().find_kernel_region_spec() matches Some((kstart, kend))
            && self.get_elf() matches Some(elf_file) ==> elf_file.wf_with_load_base(kstart)
            && elf_file.wf_with_ms(kstart, ms)
    }
}

impl WellFormed for Stage2LaunchInfo {
    open spec fn wf(&self) -> bool {
        // The Stage2LaunchInfo is well-formed if the addresses are aligned.
        &&& self.vtom % PAGE_SIZE == 0
        &&& self.cpuid_page % PAGE_SIZE as u32 == 0
        &&& self.cpuid_page != 0
        &&& self.secrets_page % PAGE_SIZE as u32 == 0
        &&& self.secrets_page != 0
        &&& self.stage2_end % PAGE_SIZE as u32 == 0
        &&& self.kernel_elf_start % PAGE_SIZE as u32 == 0
        &&& self.kernel_elf_end % PAGE_SIZE as u32 == 0
        &&& self.kernel_elf_start <= self.kernel_elf_end <= u32::MAX
        &&& self.platform_type == 0x0001 || self.platform_type == 0x0002
        &&& self.platform_type matches 0x0001 ==> self.vtom != 0
        &&& self.stage2_end > STAGE2_START
        &&& self.stage2_end <= u32::MAX  // ensures no overflow.
        &&& self.get_igvm_params_spec().wf()
        &&& self.get_igvm_param_block_spec().wf()
    }
}

impl WellFormed for DekoKernelLaunchInfo {
    open spec fn wf(&self) -> bool {
        &&& self.kernel_region_phys_start@ % PAGE_SIZE == 0
        &&& self.kernel_region_phys_end@ % PAGE_SIZE == 0
        &&& self.kernel_region_phys_start@ < self.kernel_region_phys_end@
        &&& self.heap_area_phys_start@ % PAGE_SIZE == 0
        &&& self.heap_area_size@ % PAGE_SIZE == 0
        &&& self.heap_area_size@ > 0
        &&& self.heap_area_phys_start@ + self.heap_area_size@ <= self.kernel_region_phys_end@
        &&& self.heap_area_virt_start@ + self.heap_area_size@ <= u64::MAX
        &&& self.heap_area_virt_start@ >= VADDR_UPPER_MASK
        &&& self.heap_area_virt_start@ % PAGE_SIZE == 0
        &&& self.kernel_region_virt_start@ % PAGE_SIZE == 0
        &&& self.kernel_elf_stage2_virt_start@ % PAGE_SIZE == 0
        &&& self.kernel_elf_stage2_virt_end@ % PAGE_SIZE == 0
        &&& self.kernel_elf_stage2_virt_start@ < self.kernel_elf_stage2_virt_end@
        &&& self.kernel_region_phys_start@ < self.kernel_region_phys_end@ <= 0x000f_ffff_ffff_f000
        &&& valid_heap_param(self.heap_area_virt_start@, self.heap_area_size@, HEAP_SIZE as u64)
        &&& self.debug_serial_port + 8 <= u16::MAX
    }
}

#[verifier::external_body]
#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<&crate::cpu::DekoCpuCtxPermission>,
    requires
        igvm_params_vaddr.wf(),
        ctx_perm.wf(),
        ctx_perm.pgtable_perm.mapped(igvm_params_vaddr),
    ensures
        r.wf(),
)]
pub fn get_igvm_params<'a>(igvm_params_vaddr: VirtAddr) -> IgvmParams<'a> {
    let igvm_params_block = unsafe { &*(igvm_params_vaddr.0 as *const IgvmParamBlock) };
    let igvm_params_page_vaddr = igvm_params_vaddr.0 + igvm_params_block.param_page_offset as u64;
    let igvm_params_page = unsafe { &*(igvm_params_page_vaddr as *const IgvmParamPage) };
    let memory_map_vaddr = igvm_params_vaddr.0 + igvm_params_block.memory_map_offset as u64;
    let memory_map = unsafe { &*(memory_map_vaddr as *const IgvmMemoryMap) };
    let madt_vaddr = igvm_params_vaddr.0 + igvm_params_block.madt_offset as u64;
    let madt = if igvm_params_block.madt_size == 0 {
        Some(
            unsafe {
                core::slice::from_raw_parts(
                    madt_vaddr as *const u8,
                    igvm_params_block.madt_size as usize,
                )
            },
        )
    } else {
        None
    };
    let guest_context = if igvm_params_block.guest_context_offset != 0 {
        Some(
            unsafe {
                &*((igvm_params_vaddr.0
                    + igvm_params_block.guest_context_offset as u64) as *const IgvmGuestContext)
            },
        )
    } else {
        None
    };

    IgvmParams {
        igvm_param_block: igvm_params_block,
        igvm_param_page: igvm_params_page,
        igvm_memory_map: memory_map,
        igvm_madt: madt,
        igvm_guest_context: guest_context,
    }
}

} // verus!
#[macro_export]
macro_rules! kunimplemented {
    () => {{
        $crate::kerror!("Unimplemented code at ", core::file!(), ":", core::line!());
        $crate::die("");
    }};

    ($msg:tt) => {{
        $crate::kerror!("Unimplemented code at ", core::file!(), ":", core::line!(), ": ", $msg);
        $crate::die("");
    }};
}

#[macro_export]
macro_rules! ktodo {
    () => {{
        $crate::kerror!("TODO at ", core::file!(), ":", core::line!());
        $crate::die("");
    }};

    (($msg:tt)*) => {{
        $crate::kerror!("TODO at ", core::file!(), ":", core::line!(), ": ", $msg);
        $crate::die("");
    }};
}

#[macro_export]
macro_rules! kpanic_if {
    ($cond:expr, $($msg:expr,)+) => {
        if $cond {
            $crate::kerror!("Panic at ", core::file!(), ":", core::line!(), ": ", $($msg)+);
            $crate::die("");
        }
    };

    ($cond:expr) => {
        if $cond {
            $crate::kerror!("Panic at ", core::file!(), ":", core::line!());
            $crate::die("");
        }
    };
}
