//! The Global Descriptor Table (GDT) is a binary data structure specific to the
//! IA-32 and x86-64 architectures. It contains entries telling the CPU about
//! memory segments.
//!
//! We have prepared an area in assembly code (see `stage2.S`) for GDT and this
//! module provides the Rust interface to it for initialization and loading.
use deko_std::prelude::*;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy)]
#[repr(C)]
pub struct GDTEntry(u64);

#[repr(C, packed(2))]
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
    #[inline(always)]
    pub const fn null() -> Self {
        GDTEntry(0)
    }

    #[inline(always)]
    pub const fn code_64_kernel() -> Self {
        Self(0x00af9b000000ffffu64)
    }

    #[inline(always)]
    pub const fn data_64_kernel() -> Self {
        Self(0x00cf93000000ffffu64)
    }

    #[inline(always)]
    pub const fn code_64_user() -> Self {
        Self(0x00affb000000ffffu64)
    }

    #[inline(always)]
    pub const fn data_64_user() -> Self {
        Self(0x00cff3000000ffffu64)
    }

    pub const fn tss_desc_64(tss_base: u64, tss_limit: u32) -> (Self, Self) {
        let limit_low = (tss_limit & 0xFFFF) as u64;
        let base_low = ((tss_base & 0xFFFF) as u64) << 16;
        let base_mid = (((tss_base >> 16) & 0xFF) as u64) << 32;

        // 0x89 = Present(1) | DPL(00) | Type(1001, 64-bit TSS)
        let type_attr = 0x89u64 << 40;

        let limit_high = (((tss_limit >> 16) & 0x0F) as u64) << 48;
        let attr_high = 0x00u64 << 52;  // Granularity = 0 (Byte limit)
        let base_high = (((tss_base >> 24) & 0xFF) as u64) << 56;

        let low_entry = limit_low | base_low | base_mid | type_attr | limit_high | attr_high
            | base_high;
        let high_entry = tss_base >> 32;

        (Self(low_entry), Self(high_entry))
    }
}

#[repr(C)]
pub struct GlobalDescriptorTable {
    pub entries: Array<GDTEntry, 8>,  // there are 8 entries in our GDT
}

impl WellFormed for GlobalDescriptorTable {
    closed spec fn wf(&self) -> bool {
        self.entries.wf()
    }
}

impl GlobalDescriptorTable {
    pub fn get_base_and_limit(&self) -> (u64, u16)
        requires
            self.wf(),
    {
        let base = addr_of_ref(self);

        (base as u64, (core::mem::size_of::<GDTEntry>() * 8 - 1) as u16)
    }

    #[verifier::external_body]
    pub const fn new() -> (r: Self)
        ensures
            r.wf(),
    {
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
    pub const fn new_vmpl1(tss_base: u64, tss_limit: u32) -> (r: Self)
        ensures
            r.wf(),
    {
        let (tss1, tss2) = GDTEntry::tss_desc_64(tss_base, tss_limit);

        Self {
            entries: Array::new(
                [
                    GDTEntry::null(),
                    GDTEntry::code_64_kernel(),
                    GDTEntry::data_64_kernel(),
                    GDTEntry::code_64_user(),
                    GDTEntry::data_64_user(),
                    GDTEntry::null(),
                    tss1,
                    tss2,
                ],
            ),
        }
    }

    #[verifier::external_body]
    pub fn load_selectors(&self)
        requires
            self.wf(),
    {
        self.load();

        unsafe {
            core::arch::asm!(r#"
                /* Load GDT */

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
    pub fn load(&self)
        requires
            self.wf(),
    {
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

    #[inline]
    pub fn init_gdt(cpu_perm: Tracked<&DekoCpuCore>)
        requires
            cpu_perm@.wf(),
            cpu_perm@.is_bsp(),
    {
        GLOBAL_GDT.load_selectors();
    }
}

} // verus!
verus! {

#[link_section = ".ro_after_init"]
pub exec static GLOBAL_GDT: GlobalDescriptorTable
    ensures
        GLOBAL_GDT.wf(),
{
    GlobalDescriptorTable::new()
}

} // verus!
