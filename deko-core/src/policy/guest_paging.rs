use deko_std::prelude::VirtAddr;
use deko_std::ptr::DekoPPtr;
use vstd::prelude::*;

use crate::mm::paging::{PageTable, PageTablePermission};

verus! {

#[verus_verify]
impl PageTable {
    /// Locks the page translation path for a given address in the *guest* page table
    /// by toggling the appropriate bits in the RMP table entry so that the guest is
    /// deprived of the ability to modify the page table translation for the given
    /// address to prevent potential re-mapping attacks.
    #[verus_spec(
        with
            Tracked(g_pgtable_perm): Tracked<&mut PageTablePermission>,
    )]
    pub fn lock_page_translation(ptr: DekoPPtr<PageTable>, vaddr: VirtAddr) {
    }
}

} // verus!
