use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::address::{create_paddr_range, PhysAddr, VirtAddr};
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto};
use deko_std::prelude::{PAGE_SIZE, VADDR_UPPER_MASK};
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::sync::{DekoAtomicData, DekoOnceCell, DekoSimpleOnceCell};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::collections::Vec;
use crate::guest::{DekoGuestServError, DekoGuestServResult};
use crate::imp::{RmpFlags, Rmp_ALL_BITS};
use crate::mm::check_within_guest_mmap;
use crate::mm::paging::{
    self, index_at_level, page_size_is_4kb, Page, PageTable, PageTableEntry, PageTablePath,
    PageTablePermission,
};
use crate::mm::vm::TempMapping;
use crate::policy::RECURSIVE_INDEX;
use crate::snp::rmp;
use crate::{kerror, kunimplemented, path, vec};

verus! {

#[derive(PartialEq, Eq, Clone, Copy, DekoDebug)]
pub struct GuestPageOffsetBase(pub u64);

pub exec static GUEST_PAGE_OFFSET_BASE: DekoOnceCell<
    GuestPageOffsetBase,
    (),
    GuestPageOffsetBasePred,
>
    ensures
        GUEST_PAGE_OFFSET_BASE.wf(),
{
    DekoOnceCell::new(Ghost(GuestPageOffsetBasePred {  }))
}

impl WellFormed for GuestPageOffsetBase {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        self.0 >= VADDR_UPPER_MASK && self.0 % PAGE_SIZE == 0
    }
}

with_atomic_pred!(
    GuestPageOffsetBase,
    (),
    fields: {},
    perm_fields: {},
    data.wf()
);

/// This function is untrusted since the base comes from the guest.
#[inline(always)]
#[verus_spec(r =>
    requires
        phys_addr.wf(),
    ensures
        // r.wf(),
)]
pub fn guest_phys_to_virt(phys_addr: PhysAddr) -> Option<VirtAddr> {
    match GUEST_PAGE_OFFSET_BASE.get() {
        Some(DekoAtomicData { data: GuestPageOffsetBase(base), .. }) => {
            if core::hint::likely(phys_addr.0 < u64::MAX - base) {
                Some(VirtAddr(phys_addr.0 + base))
            } else {
                None
            }
        },
        None => None,
    }
}

#[derive(DekoDebug)]
pub struct GuestMapping {
    /// The level of the page table where the mapping was found.
    pub lvl: usize,
    /// Temporary mappings used for guest page table walks.
    /// Should be dropped when done.
    ///
    /// Why is this needed? This is because the intermediate PTEs are
    /// not mapped in our own page table, so we need to create temporary
    /// mappings to access them.
    pub temp_mappings: Vec<TempMapping>,
}

impl WellFormed for GuestMapping {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.temp_mappings.wf()
        &&& self.temp_mappings@.len() <= 4
        &&& forall|i: int|
            #![trigger self.temp_mappings@[i]]
            0 <= i < self.temp_mappings@.len() ==> {
                self.temp_mappings@[i].inner.end@ - self.temp_mappings@[i].inner.start@ == PAGE_SIZE
            }
    }
}

impl GuestMapping {
    /// Returns the most recent temporary mapping created during the page table walk.
    ///
    /// The order is reversed compared to the order in which they were created.
    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
        ensures
            self.temp_mappings.len() > 0 ==> {
                &&& r matches Some(tm) && tm == self.temp_mappings@[0]
            },
            self.temp_mappings.len() == 0 ==> {
                r is None
            }
    )]
    pub fn final_mapping(&self) -> Option<&TempMapping> {
        self.temp_mappings.first()
    }

    /// Locks the page translation path for a given address in the *guest* page table
    /// by toggling the appropriate bits in the RMP table entry so that the guest is
    /// deprived of the ability to modify the page table translation for the given
    /// address to prevent potential re-mapping attacks.
    #[verus_spec(
        requires
            self.wf(),
            self.temp_mappings.len() > 0,
    )]
    pub fn lock_translation_path(&self) -> DekoGuestServResult<()> {
        broadcast use RmpFlags::lemma_each_bit_is_valid;

        proof {
            bit_u32_and_auto();
            bit_u64_and_auto();
        }

        let rmp_flags = RmpFlags::from_bits_truncate(
            RmpFlags::rx_guest_vmpl2().bits() | RmpFlags::rwx_guest_vmpl1().bits()
                | RmpFlags::rwx().bits(),  /* for vmpl0 */
        );

        for i in 0..self.temp_mappings.len()
            invariant
                rmp_flags.wf(),
                rmp_flags.bits() & Rmp_ALL_BITS == rmp_flags.bits(),
        {
        }

        Ok(())
    }
}

#[verus_verify]
impl Page {
    /// Creates a temporary mapping from a guest page table entry.
    #[verus_spec(r =>
        with
            Tracked(pte_perm): Tracked<&DekoPointsTo<PageTableEntry>>,
        requires
            pte_perm.wf(),
            pte_perm.is_init(),
            pte_perm.pptr() == pte@,
        ensures
            r matches Ok(tm) ==> {
                &&& tm.wf()
                &&& tm.inner.end@ - tm.inner.start@ == PAGE_SIZE
            }
    )]
    fn from_guest_entry(
        pte: DekoPPtr<PageTableEntry>,
        private_bit: u64,
        shared_bit: u64,
    ) -> DekoGuestServResult<TempMapping> {
        let val = pte.borrow(Tracked(pte_perm));
        let paddr = val.address(private_bit, shared_bit);

        if core::hint::unlikely(!check_within_guest_mmap(paddr)) {
            kerror!("Guest created unmapped memory at physical address", paddr);

            return Err(DekoGuestServError::FatalError);
        }
        if core::hint::unlikely(paddr.0 >= 0x0000_FFFF_FFFF_F000u64 || paddr.0 % PAGE_SIZE != 0) {
            kerror!("Guest created invalid physical address", paddr);

            return Err(DekoGuestServError::FatalError);
        }
        TempMapping::new(create_paddr_range(paddr, 1)).ok_or(DekoGuestServError::FatalError)
    }
}

#[verus_verify]
impl PageTable {
    /// Walks the guest page table to resolve the given guest virtual address.
    ///
    /// Note that this function does not behave the same way as the normal way
    /// we walk our own page tables. This is because the guest page tables
    /// may not be fully mapped in our own page tables, so we need to create
    /// temporary mappings to access the guest page tables.
    ///
    /// Furthermore, since the guest page table is not controlled by us, there
    /// is simply no guarantee that the walk is "semantically meaningful". This
    /// is acceptable, though, because if this will NEVER hurt the security of
    /// our system - at worst, we can simply crash if it tries to
    /// access invalid memory.
    #[verus_spec(r =>
        requires
            g_page_table.wf(),
            g_page_table.inner.end@ - g_page_table.inner.start@ == PAGE_SIZE,
        ensures
            r matches Ok(gm) ==> {
                &&& gm.temp_mappings@.len() <= 4
                &&& gm.wf()
            }
    )]
    pub fn walk_lvl3_guest(
        g_page_table: &TempMapping,
        g_vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,  /* f: Option<F> where F: Fn(PhysAddr), */
    ) -> DekoGuestServResult<GuestMapping> {
        proof {
            page_size_is_4kb();
        }

        let idx = index_at_level::<3>(g_vaddr);
        let this_page_table = g_page_table.read_ref::<Page>();

        proof {
            assume(this_page_table.0.wf());
        }

        let (entry, Tracked(entry_perm)) = this_page_table.0.index_as_ptr(idx);

        if !PageTableEntry::is_valid_pte(entry, Tracked(&entry_perm)) {
            // If we reached a huge page here we still need to return a mapping.
            Ok(
                GuestMapping {
                    lvl: 3,
                    temp_mappings: {
                        if PageTableEntry::is_huge_pte(entry, Tracked(&entry_perm))
                            && PageTableEntry::is_present_pte(entry, Tracked(&entry_perm)) {
                            proof_with!(Tracked(&entry_perm));
                            let mapping = Page::from_guest_entry(entry, private_bit, shared_bit)?;
                            vec![mapping]
                        } else {
                            vec![]
                        }
                    },
                },
            )
        } else {
            proof_with!(Tracked(&entry_perm));
            let next_mapping = Page::from_guest_entry(entry, private_bit, shared_bit)?;
            let mut guest_mapping = PageTable::walk_lvl2_guest(
                &next_mapping,
                g_vaddr,
                private_bit,
                shared_bit,
            )?;
            guest_mapping.temp_mappings.push(next_mapping);
            Ok(guest_mapping)
        }
    }

    #[verus_spec(r =>
        requires
            g_page_table.wf(),
            g_page_table.inner.end@ - g_page_table.inner.start@ == PAGE_SIZE,
        ensures
            r matches Ok(gm) ==> {
                &&& gm.temp_mappings@.len() <= 3
                &&& gm.wf()
            }
    )]
    pub fn walk_lvl2_guest(
        g_page_table: &TempMapping,
        g_vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> DekoGuestServResult<GuestMapping> {
        proof {
            page_size_is_4kb();
        }

        let idx = index_at_level::<2>(g_vaddr);
        let this_page_table = g_page_table.read_ref::<Page>();
        proof {
            assume(this_page_table.0.wf());
        }
        let (entry, Tracked(entry_perm)) = this_page_table.0.index_as_ptr(idx);

        if !PageTableEntry::is_valid_pte(entry, Tracked(&entry_perm)) {
            // If we reached a huge page here we still need to return a mapping.
            Ok(
                GuestMapping {
                    lvl: 2,
                    temp_mappings: {
                        if PageTableEntry::is_huge_pte(entry, Tracked(&entry_perm))
                            && PageTableEntry::is_present_pte(entry, Tracked(&entry_perm)) {
                            proof_with!(Tracked(&entry_perm));
                            let mapping = Page::from_guest_entry(entry, private_bit, shared_bit)?;
                            vec![mapping]
                        } else {
                            vec![]
                        }
                    },
                },
            )
        } else {
            proof_with!(Tracked(&entry_perm));
            let next_mapping = Page::from_guest_entry(entry, private_bit, shared_bit)?;
            let mut guest_mapping = PageTable::walk_lvl1_guest(
                &next_mapping,
                g_vaddr,
                private_bit,
                shared_bit,
            )?;
            guest_mapping.temp_mappings.push(next_mapping);
            Ok(guest_mapping)
        }
    }

    #[verus_spec(r =>
        requires
            g_page_table.wf(),
            g_page_table.inner.end@ - g_page_table.inner.start@ == PAGE_SIZE,
        ensures
            r matches Ok(gm) ==> {
                &&& gm.temp_mappings@.len() <= 2
                &&& gm.wf()
            }
    )]
    pub fn walk_lvl1_guest(
        g_page_table: &TempMapping,
        g_vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> DekoGuestServResult<GuestMapping> {
        proof {
            page_size_is_4kb();
        }

        let idx = index_at_level::<1>(g_vaddr);
        let this_page_table = g_page_table.read_ref::<Page>();
        proof {
            assume(this_page_table.0.wf());
        }

        let (entry, Tracked(entry_perm)) = this_page_table.0.index_as_ptr(idx);

        if !PageTableEntry::is_valid_pte(entry, Tracked(&entry_perm)) {
            // If we reached a huge page here we still need to return a mapping.
            Ok(
                GuestMapping {
                    lvl: 1,
                    temp_mappings: {
                        if PageTableEntry::is_huge_pte(entry, Tracked(&entry_perm))
                            && PageTableEntry::is_present_pte(entry, Tracked(&entry_perm)) {
                            proof_with!(Tracked(&entry_perm));
                            let mapping = Page::from_guest_entry(entry, private_bit, shared_bit)?;
                            vec![mapping]
                        } else {
                            vec![]
                        }
                    },
                },
            )
        } else {
            proof_with!(Tracked(&entry_perm));
            let next_mapping = Page::from_guest_entry(entry, private_bit, shared_bit)?;
            let mut guest_mapping = PageTable::walk_lvl0_guest(
                &next_mapping,
                g_vaddr,
                private_bit,
                shared_bit,
            )?;
            guest_mapping.temp_mappings.push(next_mapping);
            Ok(guest_mapping)
        }
    }

    #[inline]
    #[verus_spec(r =>
        requires
            g_page_table.wf(),
            g_page_table.inner.end@ - g_page_table.inner.start@ == PAGE_SIZE,
        ensures
            r matches Ok(gm) ==> {
                &&& gm.temp_mappings@.len() <= 1
                &&& gm.wf()
            }
    )]
    fn walk_lvl0_guest(
        g_page_table: &TempMapping,
        g_vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> DekoGuestServResult<GuestMapping> {
        proof {
            page_size_is_4kb();
        }

        let idx = index_at_level::<0>(g_vaddr);
        let this_page_table = g_page_table.read_ref::<Page>();

        proof {
            assume(this_page_table.0.wf());
        }

        let (entry, Tracked(entry_perm)) = this_page_table.0.index_as_ptr(idx);

        Ok(
            GuestMapping {
                lvl: 0,
                temp_mappings: {
                    if PageTableEntry::is_present_pte(entry, Tracked(&entry_perm)) {
                        proof_with!(Tracked(&entry_perm));
                        let mapping = Page::from_guest_entry(entry, private_bit, shared_bit)?;
                        vec![mapping]
                    } else {
                        vec![]
                    }
                },
            },
        )
    }
}

} // verus!
