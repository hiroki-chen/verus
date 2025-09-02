use deko_std::prelude::*;
use vstd::prelude::*;

core::arch::global_asm!(include_str!("idt.S"), options(att_syntax));

verus! {

pub const DE_VECTOR: usize = 0;

pub const DB_VECTOR: usize = 1;

pub const NMI_VECTOR: usize = 2;

pub const BP_VECTOR: usize = 3;

pub const OF_VECTOR: usize = 4;

pub const BR_VECTOR: usize = 5;

pub const UD_VECTOR: usize = 6;

pub const NM_VECTOR: usize = 7;

pub const DF_VECTOR: usize = 8;

pub const CSO_VECTOR: usize = 9;

pub const TS_VECTOR: usize = 10;

pub const NP_VECTOR: usize = 11;

pub const SS_VECTOR: usize = 12;

pub const GP_VECTOR: usize = 13;

pub const PF_VECTOR: usize = 14;

pub const MF_VECTOR: usize = 16;

pub const AC_VECTOR: usize = 17;

pub const MCE_VECTOR: usize = 18;

pub const XF_VECTOR: usize = 19;

pub const VE_VECTOR: usize = 20;

pub const CP_VECTOR: usize = 21;

pub const HV_VECTOR: usize = 28;

pub const VC_VECTOR: usize = 29;

pub const SX_VECTOR: usize = 30;

pub const INT_INJ_VECTOR: usize = 0x50;

pub const IPI_VECTOR: usize = 0xE0;

const IDT_TARGET_MASK_1: u64 = 0x0000_0000_0000_ffff;

const IDT_TARGET_MASK_2: u64 = 0x0000_0000_ffff_0000;

const IDT_TARGET_MASK_3: u64 = 0xffff_ffff_0000_0000;

const IDT_TARGET_MASK_1_SHIFT: u64 = 0;

const IDT_TARGET_MASK_2_SHIFT: u64 = 48 - 16;

const IDT_TARGET_MASK_3_SHIFT: u64 = 32;

const IDT_TYPE_MASK: u8 = 0x0f;

const IDT_TYPE_SHIFT: u64 = 40;

const IDT_TYPE_CALL: u8 = 0x0c;

const IDT_TYPE_INT: u8 = 0x0e;

const IDT_TYPE_TRAP: u8 = 0x0f;

pub fn create_early_idt() -> (arr: Array<IdtEntry, 256>)
    ensures
        arr.wf(),
        forall|i: int|
            0 <= i && i < 256 ==> #[trigger] arr@[i as int].high == 0 && arr@[i as int].low == 0,
{
    Array::fill(IdtEntry::no_handler())
}

/// The base addresses of the IDT should be aligned on an 8-byte boundary
/// to maximize performance of cache line fills.
#[repr(C, packed(8))]
#[derive(Copy, Clone)]
pub struct IdtEntry {
    pub low: u64,
    pub high: u64,
}

impl WellFormed for IdtEntry {
    closed spec fn wf(&self) -> bool {
        true
    }
}

impl IdtEntry {
    pub const fn no_handler() -> (r: Self)
        ensures
            r.wf(),
            r.low == 0,
            r.high == 0,
    {
        Self { low: 0, high: 0 }
    }

    fn create(target: VirtAddr, cs: u16, desc_type: u8, dpl: u8, ist: u8) -> Self {
        let vaddr = target.0 as u64;
        let cs_mask = (cs as u64) << IDT_CS_SHIFT;
        let ist_mask = ((ist as u64) & IDT_IST_MASK) << IDT_IST_SHIFT;
        let low = (vaddr & IDT_TARGET_MASK_1) << IDT_TARGET_MASK_1_SHIFT | (vaddr
            & IDT_TARGET_MASK_2) << IDT_TARGET_MASK_2_SHIFT | idt_type_mask(desc_type)
            | IDT_PRESENT_MASK | idt_dpl_mask(dpl) | cs_mask | ist_mask;
        let high = (vaddr & IDT_TARGET_MASK_3) >> IDT_TARGET_MASK_3_SHIFT;

        IdtEntry { low, high }
    }

    #[inline(always)]
    pub fn raw_entry(target: VirtAddr) -> Self {
        Self::create(target, 8, IDT_TYPE_INT, 0, 0)
    }
}

fn idt_type_mask(t: u8) -> u64 {
    ((t & IDT_TYPE_MASK) as u64) << IDT_TYPE_SHIFT
}

const IDT_DPL_MASK: u8 = 0x03;

const IDT_DPL_SHIFT: u64 = 45;

fn idt_dpl_mask(dpl: u8) -> u64 {
    ((dpl & IDT_DPL_MASK) as u64) << IDT_DPL_SHIFT
}

const IDT_PRESENT_MASK: u64 = 0x1u64 << 47;

const IDT_CS_SHIFT: u64 = 16;

const IDT_IST_MASK: u64 = 0x7;

const IDT_IST_SHIFT: u64 = 32;

#[repr(C, packed(2))]
#[derive(Default, Clone, Copy)]
struct IdtDesc {
    limit: u16,
    address: VirtAddr,
}

pub struct Idt {
    pub entries: Array<IdtEntry, 256>,
}

impl WellFormed for Idt {
    closed spec fn wf(&self) -> bool {
        &&& self.entries.wf()
        &&& forall|i: int|
            0 <= i && i < 256 ==> #[trigger] self.entries@[i as int].high != 0
                || self.entries@[i as int].low != 0
    }
}

impl View for Idt {
    type V = Array<IdtEntry, 256>;

    closed spec fn view(&self) -> Self::V {
        self.entries
    }
}

impl Idt {
    /// Load an IDT.
    ///
    /// # Safety
    ///
    /// Since we have no guarantee that the IDT is valid, this function is unsafe.
    /// The caller must ensure that the IDT is valid before calling this function.
    #[verifier::external_body]
    pub fn load(&self)
        requires
            self.wf(),
    {
        let base: *const IdtEntry = self.entries.index(0);
        let limit = core::mem::size_of::<IdtEntry>() * 256 - 1;

        let desc = IdtDesc { limit: limit as u16, address: VirtAddr::from(base) };

        unsafe {
            core::arch::asm!(
                "lidt (%rax)",
                in("rax") &desc,
                options(att_syntax),
            );
        }
    }

    /// Initialize an IDT entry.
    pub fn init(&mut self, addr: *const u8, size: usize)
        requires
            addr as usize + size * 32 <= usize::MAX,
            size <= old(self).entries@.len(),
            old(self).entries.wf(),
        ensures
            forall|i: int| 0 <= i < size as int ==> #[trigger] self.entries@[i as int].wf(),
    {
        let mut i = 0;
        let addr = addr as usize;

        while i < size
            invariant
                0 <= i <= size,
                size <= self.entries@.len(),
                addr + size * 32 <= usize::MAX,
                addr + i * 32 <= usize::MAX,
                old(self).entries@.len() == self.entries@.len(),
                self.entries.wf(),
            decreases size - i,
        {
            let this_addr = VirtAddr::from((addr as usize + i * 32) as u64);

            self.entries.update(i, IdtEntry::raw_entry(this_addr));

            i += 1;
        }
    }

    #[inline(always)]
    pub fn from_idt_entries(entries: Array<IdtEntry, 256>) -> (r: Self)
        requires
            entries.wf(),
            forall|i: int|
                0 <= i && i < 256 ==> #[trigger] entries@[i as int].high != 0
                    || entries@[i as int].low != 0,
        ensures
            r.wf(),
    {
        Idt { entries }
    }
}

/// Initialize the early IDT used in stage2. This will remain in scope as long as
/// stage2 is in memory.
#[verifier::external_body]
pub fn init_early_idt(early_idt: &mut Idt)
    requires
        old(early_idt).entries.wf(),
    ensures
        early_idt.wf(),
{
    unsafe {
        early_idt.init(
            &stage2_generic_idt_handler_no_ghcb as *const u8,
            core::mem::size_of::<IdtEntry>(),
        );
    }

    early_idt.load();
}

#[verifier::external_body]
pub fn init_generic_idt(early_idt: &mut Idt)
    requires
        old(early_idt).wf(),  // since we must have called init_early_idt

    ensures
        early_idt.wf(),
{
    unsafe {
        early_idt.init(&stage2_generic_idt_handler as *const u8, core::mem::size_of::<IdtEntry>());
    }

    early_idt.load();
}

#[verusfmt::skip]
extern "C" {
    pub static stage2_generic_idt_handler_no_ghcb: u8;
    pub static stage2_generic_idt_handler: u8;
}

} // verus!
