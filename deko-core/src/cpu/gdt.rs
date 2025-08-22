//! The Global Descriptor Table (GDT) is a binary data structure specific to the
//! IA-32 and x86-64 architectures. It contains entries telling the CPU about
//! memory segments.
//!
//! We have prepared an area in assembly code (see `stage2.S`) for GDT and this
//! module provides the Rust interface to it for initialization and loading.
use deko_std::prelude::*;
use vstd::prelude::*;

use crate::address::VirtAddr;

verus! {

#[link_section = ".ro_after_init"]
pub exec static GLOBAL_GDT: GlobalDescriptorTable = GlobalDescriptorTable::new();

#[derive(Clone, Copy)]
#[repr(C)]
pub struct GDTEntry(u64);

#[repr(C)]
pub struct GDTDesc {
    limit: u16,
    base: VirtAddr,
}

impl WellFormed for GDTEntry {
    closed spec fn wf(&self) -> bool {
        true
    }
}

impl GDTEntry {
    pub const fn null() -> Self {
        GDTEntry(0)
    }

    pub const fn code_64_kernel() -> Self {
        Self(0x00af9b000000ffffu64)
    }

    pub const fn data_64_kernel() -> Self {
        Self(0x00cf93000000ffffu64)
    }

    pub const fn code_64_user() -> Self {
        Self(0x00affb000000ffffu64)
    }

    pub const fn data_64_user() -> Self {
        Self(0x00cff3000000ffffu64)
    }
}

pub struct GlobalDescriptorTable {
    pub entries: Array<GDTEntry, 8>,  // there are 8 entries in our GDT
}

impl WellFormed for GlobalDescriptorTable {
    closed spec fn wf(&self) -> bool {
        self.entries.wf()
    }
}

impl GlobalDescriptorTable {
    #[verifier::external_body]
    pub const fn new() -> Self {
        Self {
            entries: Array::new(
                [
                    GDTEntry::null(),
                    GDTEntry::code_64_kernel(),
                    GDTEntry::data_64_kernel(),
                    GDTEntry::code_64_user(),
                    GDTEntry::data_64_user(),
                    GDTEntry::null(),
                    GDTEntry::null(),
                    GDTEntry::null(),
                ],
            ),
        }
    }

    #[verifier::external_body]
    pub fn load_selectors(&self) {
        self.load();

        unsafe {
            core::arch::asm!(r#" /* Load GDT */

            /* Reload data segments */
                 movw   %cx, %ds
                 movw   %cx, %es
                 movw   %cx, %fs
                 movw   %cx, %gs
                 movw   %cx, %ss

                 /* Reload code segment */
                 pushq  %rdx
                 leaq   1f(%rip), %rax
                 pushq  %rax
                 lretq
            1:
                 "#,
                in("rdx") 8,
                in("rcx") 16,
                options(att_syntax));
        }
    }

    #[verifier::external_body]
    pub fn load(&self) {
        let desc = GDTDesc {
            limit: (core::mem::size_of::<GDTEntry>() * 8 - 1) as u16,
            base: VirtAddr::from(&self.entries as *const _),
        };

        unsafe {
            core::arch::asm!(
                "lgdt ({0})", // load the address of our GDT
                in(reg) &desc,
                options(att_syntax),
            );
        }
    }
}

pub fn init_gdt() {
    GLOBAL_GDT.load_selectors();
}

} // verus!
