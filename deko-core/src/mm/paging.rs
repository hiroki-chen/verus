// use deko_std::prelude::*;
// use vstd::prelude::*;
// use crate::mm::*;
// unsafe extern "C" {
//     /// This is the initial page table set up before the stage2 code is even run.
//     /// For interested readers please see `stage2.S` file for more information.
//     ///
//     /// This page table constructs a very simple identity mapping from virtual
//     /// address to their physical address for the entire physical memory. Please
//     /// also note that this papge table uses 2MB page for the PD level.
//     ///
//     /// It is always safe to access this page table since it is repr(C).
//     #[link_name = "pgtable"]
//     static mut initial_page_table: PageTable;
// }
// verus! {
// pub ghost struct DekoCpuPTOwner {
//     pub cpu_id: u64,
//     pub pgtable: u64,
// }
// impl WellFormed for DekoCpuPTOwner {
//     open spec fn wf(&self) -> bool {
//         true
//     }
// }
// impl DekoCpuPTOwner {
//     pub open spec fn new(cpu_id: u64, pt: u64) -> Self {
//         DekoCpuPTOwner { cpu_id, pgtable: pt }
//     }
//     pub open spec fn cpu_id(&self) -> u64 {
//         self.cpu_id
//     }
//     pub open spec fn pgtable(&self) -> u64 {
//         self.pgtable
//     }
// }
// impl Ptebehavior for PageTableEntry {
//     #[inline]
//     pub fn page_frame(&self) -> PhysAddr {
//         PhysAddr(strip_confidentiality_bits(self.0.0 & 0x000f_ffff_ffff_f000))
//     }
//     /// Get the address from the page table entry, excluding the C/shared bit.
//     #[inline]
//     pub fn address(&self) -> PhysAddr {
//         PhysAddr(strip_shared_address_bits(self.page_frame().0))
//     }
//     pub open spec fn is_valid_pte_spec(&self) -> bool {
//         let bits = from_bits(self.0);
//         bits.contains(Pte::PRESENT) && !bits.contains(Pte::HUGE)
//     }
//     pub open spec fn is_huge_pte_spec(&self) -> bool {
//         let bits = from_bits(self.0);
//         bits.contains(Pte::HUGE)
//     }
//     pub open spec fn is_present_pte_spec(&self) -> bool {
//         let bits = from_bits(self.0);
//         bits.contains(Pte::PRESENT)
//     }
//     pub fn is_present_pte(
//         pte: DekoPPtr<PageTableEntry>,
//         Tracked(perm): Tracked<&DekoPointsTo<PageTableEntry>>,
//     ) -> (r: bool)
//         requires
//             pte@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//         ensures
//             r == Self::is_present_pte_spec(*perm),
//     {
//         broadcast use PteFlags::lemma_each_bits_is_valid;
//         let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
//         flags.contains(PRESENT)
//     }
//     /// This function checks whether a given PTE is valid in the sense that
//     /// it is either not present, or it is huge page so that we will need to
//     /// take extra care when handling it.
//     pub fn is_valid_pte(
//         pte: DekoPPtr<PageTableEntry>,
//         Tracked(perm): Tracked<&DekoPointsTo<PageTableEntry>>,
//     ) -> (r: bool)
//         requires
//             pte@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//         ensures
//             r == Self::is_valid_pte_spec(*perm),
//     {
//         broadcast use PteFlags::lemma_each_bits_is_valid;
//         let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
//         flags.contains(PRESENT) && !flags.contains(HUGE)
//     }
//     pub fn is_huge_pte(
//         pte: DekoPPtr<PageTableEntry>,
//         Tracked(perm): Tracked<&DekoPointsTo<PageTableEntry>>,
//     ) -> (r: bool)
//         requires
//             pte@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//         ensures
//             r == Self::is_huge_pte_spec(*perm),
//     {
//         broadcast use PteFlags::lemma_each_bits_is_valid;
//         let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
//         flags.contains(HUGE)
//     }
// }
// impl PageTable {
//     pub open spec fn walk_spec(vaddr: VirtAddr) -> (DekoPPtr<PageTableEntry>, PagePermissionIndex) {
//         // Walk the page table hierarchy starting from level 3 (PML4)
//         // and return the deepest level mapping that is present
//         Self::walk_level_spec(3, vaddr)
//     }
//     /// Recursive specification for walking page table levels
//     pub open spec fn walk_level_spec(level: nat, vaddr: VirtAddr) -> (
//         DekoPPtr<PageTableEntry>,
//         PagePermissionIndex,
//     )
//         recommends
//             level <= 3,
//         decreases level,
//     {
//         let idx = index_at_level_spec(level, vaddr);
//         match level as u64 {
//             3 => {
//                 // Level 3 (PML4): Check if entry is present and not huge
//                 if Self::is_entry_present_and_valid_spec(3, idx) {
//                     // Entry is present and points to next level, recurse to level 2
//                     Self::walk_level_spec(2, vaddr)
//                 } else {
//                     // Entry is not present or is a huge page, return level 3 mapping
//                     (Self::get_pte_ptr_spec(3, idx), (3, idx as int))
//                 }
//             },
//             2 => {
//                 // Level 2 (PDPT): Check if entry is present and not huge
//                 if Self::is_entry_present_and_valid_spec(2, idx) {
//                     // Entry is present and points to next level, recurse to level 1
//                     Self::walk_level_spec(1, vaddr)
//                 } else {
//                     // Entry is not present or is a huge page (1GB), return level 2 mapping
//                     (Self::get_pte_ptr_spec(2, idx), (2, idx as int))
//                 }
//             },
//             1 => {
//                 // Level 1 (PD): Check if entry is present and not huge
//                 if Self::is_entry_present_and_valid_spec(1, idx) {
//                     // Entry is present and points to next level, recurse to level 0
//                     Self::walk_level_spec(0, vaddr)
//                 } else {
//                     // Entry is not present or is a huge page (2MB), return level 1 mapping
//                     (Self::get_pte_ptr_spec(1, idx), (1, idx as int))
//                 }
//             },
//             0 => {
//                 // Level 0 (PT): This is the leaf level, always return level 0 mapping
//                 (Self::get_pte_ptr_spec(0, idx), (0, idx as int))
//             },
//             _ => {
//                 // Invalid level, should not happen due to precondition
//                 arbitrary()
//             },
//         }
//     }
//     /// Specification for checking if a page table entry is present and valid (not huge)
//     /// This determines whether we can continue walking to the next level
//     pub open spec fn is_entry_present_and_valid_spec(level: nat, idx: nat) -> bool
//         recommends
//             level <= 3,
//             idx < PAGE_TABLE_ENTRY,
//     {
//         // This is an abstract specification that represents:
//         // 1. The entry at (level, idx) has the PRESENT bit set
//         // 2. The entry does not have the HUGE bit set (so we can walk to next level)
//         // In the actual implementation, this would read the PTE and check the bits
//         arbitrary()
//     }
//     /// Specification for getting a pointer to a page table entry at a given level and index
//     pub open spec fn get_pte_ptr_spec(level: nat, idx: nat) -> DekoPPtr<PageTableEntry>
//         recommends
//             level <= 3,
//             idx < PAGE_TABLE_ENTRY,
//     {
//         // This is an abstract specification that represents getting a pointer
//         // to the page table entry at the specified level and index
//         // In the actual implementation, this would calculate the virtual address
//         // of the PTE based on the page table self-mapping
//         arbitrary()
//     }
//     #[inline]
//     /// Walk the page table at the given virtual address `vaddr` and return
//     /// the mapping at the lowest possible level (in the sense that it is
//     /// present in the entry).
//     pub fn walk(
//         pgtable: DekoPPtr<PageTable>,
//         Tracked(perm): Tracked<DekoPointsTo<Page>>,
//         vaddr: VirtAddr,
//     ) -> (r: Mapping)
//         requires
//             pgtable@ == perm.pptr(),
//             pgtable.addr() + 0x1000 <= usize::MAX,
//             perm.wf(),
//             perm.is_init(),
//             perm.mem_wf(),
//         ensures
//             r.wf(),
//     {
//         Page::walk_level3(pgtable, Tracked(perm), vaddr)
//     }
// }
// impl Page {
//     /// When we obtain a PTE entry, we can convert it to a Page if it is
//     /// not a leaf entry. Since we will consume the token pointing to the PTE,
//     /// we guarantee that no one will be able to modify the PTE while we
//     /// are using the Page.
//     pub fn from_entry(
//         pte: DekoPPtr<PageTableEntry>,
//         Tracked(perm): Tracked<DekoPointsTo<PageTableEntry>>,
//     ) -> (r: (DekoPPtr<Page>, Tracked<DekoPointsTo<Page>>))
//         requires
//             pte@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//             PageTableEntry::is_valid_pte_spec(perm),
//         ensures
//             r.1@.pptr() == r.0@,
//             r.1@.mem_wf(),
//             r.1@.wf(),
//     {
//         let vaddr = phys_to_virt(pte.borrow(Tracked(&perm)).address());
//         unsafe {
//             // I think we should add stronger precondition to
//             // ensure that this is really 'safe'; this needs
//             // 'transmute' functionality.
//             DekoPPtr::<Page>::from_raw_init(vaddr.0)
//         }
//     }
//     fn walk_level0(
//         page: DekoPPtr<Page>,
//         Tracked(perm): Tracked<DekoPointsTo<Page>>,
//         vaddr: VirtAddr,
//     ) -> (r: Mapping)
//         requires
//             page@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//             page.addr() + 0x1000 <= usize::MAX,
//         ensures
//             r.wf(),
//     {
//         let idx = index_at_level::<0>(vaddr);
//         let borrowed_ptr = DekoPPtr(
//             vstd::simple_pptr::PPtr(page.addr() + idx * 8, core::marker::PhantomData),
//         );
//         Mapping::Level0(borrowed_ptr, Tracked((0, idx as int)))
//     }
//     fn walk_level1(
//         page: DekoPPtr<Page>,
//         Tracked(perm): Tracked<DekoPointsTo<Page>>,
//         vaddr: VirtAddr,
//     ) -> (r: Mapping)
//         requires
//             page@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//             page.addr() + 0x1000 <= usize::MAX,
//         ensures
//             r.wf(),
//     {
//         let idx = index_at_level::<1>(vaddr);
//         let (entry, Tracked(entry_perm)) = unsafe {
//             // ADD MORE
//             DekoPPtr::<PageTableEntry>::from_raw_init((page.addr() + idx * 8) as u64)
//         };
//         if PageTableEntry::is_valid_pte(entry, Tracked(&entry_perm)) {
//             let (next_page, next_perm) = Page::from_entry(entry, Tracked(entry_perm));
//             Page::walk_level0(next_page, next_perm, vaddr)
//         } else {
//             Mapping::Level1(entry, Tracked(entry_perm))
//         }
//     }
//     #[verifier::external_body]
//     fn walk_level2(
//         page: DekoPPtr<Page>,
//         Tracked(perm): Tracked<DekoPointsTo<Page>>,
//         vaddr: VirtAddr,
//     ) -> (r: Mapping)
//         requires
//             page@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//             page.addr() + 0x1000 <= usize::MAX,
//         ensures
//             r.wf(),
//     {
//         let idx = index_at_level::<2>(vaddr);
//         let (entry, Tracked(entry_perm)) = unsafe {
//             // ADD MORE
//             DekoPPtr::<PageTableEntry>::from_raw_init((page.addr() + idx * 8) as u64)
//         };
//         assume(entry_perm.is_init());
//         if PageTableEntry::is_valid_pte(entry, Tracked(&entry_perm)) {
//             let (next_page, next_perm) = Page::from_entry(entry, Tracked(entry_perm));
//             Page::walk_level1(next_page, next_perm, vaddr)
//         } else {
//             Mapping::Level2(entry, Tracked(entry_perm))
//         }
//     }
//     /// Walk the page now at the root level (level 3).
//     #[verifier::external_body]
//     fn walk_level3(
//         page: DekoPPtr<Page>,
//         Tracked(perm): Tracked<DekoPointsTo<Page>>,
//         vaddr: VirtAddr,
//     ) -> (r: Mapping)
//         requires
//             page@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//             page.addr() + 0x1000 <= usize::MAX,
//         ensures
//             r.wf(),
//     {
//         let idx = index_at_level::<3>(vaddr);
//         let (entry, Tracked(entry_perm)) = unsafe {
//             // ADD MORE
//             DekoPPtr::<PageTableEntry>::from_raw_init((page.addr() + idx * 8) as u64)
//         };
//         assume(entry_perm.is_init());
//         if PageTableEntry::is_valid_pte(entry, Tracked(&entry_perm)) {
//             let (next_page, next_perm) = Page::from_entry(entry, Tracked(entry_perm));
//             Page::walk_level2(next_page, next_perm, vaddr)
//         } else {
//             Mapping::Level3(entry, Tracked(entry_perm))
//         }
//     }
//     #[verifier::external_body]
//     fn allocate_pte_level1(
//         entry: DekoPPtr<PageTableEntry>,
//         Tracked(perm): Tracked<DekoPointsTo<PageTableEntry>>,
//         vaddr: VirtAddr,
//         huge_page: bool,
//     ) -> (r: Mapping)
//         requires
//             entry@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//             entry.addr() + 0x1000 <= usize::MAX,
//         ensures
//             r.wf(),
//     {
//         broadcast use PteFlags::lemma_each_bits_is_valid;
//         let flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&perm)).0.0);
//         if flags.contains(PRESENT) {
//             return Mapping::Level3(entry, Tracked(perm));
//         }
//         let (page, Tracked(mut page_perm)) = {
//             let (page, page_perm) = Box::<Page>::new_zeroed(&DEKO_FRAME_ALLOCATOR.0);
//             page.into_ptr(page_perm)
//         };
//         let flags = PRESENT | WRITABLE | USER | ACCESSED;
//         let new_pte_value = make_private_address(page.addr() as u64) | flags;
//         let tracked mut perm = perm;
//         entry.write(Tracked(&mut perm), PageTableEntry(PhysAddr(new_pte_value)));
//         let idx = index_at_level::<0>(vaddr);
//         let next_entry = page.addr() + idx * 8;
//         let (next_entry, Tracked(next_entry_perm)) = unsafe {
//             DekoPPtr::<PageTableEntry>::from_raw_init(next_entry as u64)
//         };
//         Mapping::Level0(next_entry, Tracked(next_entry_perm))
//     }
//     #[verifier::external_body]
//     fn allocate_pte_level2(
//         entry: DekoPPtr<PageTableEntry>,
//         Tracked(perm): Tracked<DekoPointsTo<PageTableEntry>>,
//         vaddr: VirtAddr,
//         huge_page: bool,
//     ) -> (r: Mapping)
//         requires
//             entry@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//             entry.addr() + 0x1000 <= usize::MAX,
//         ensures
//             r.wf(),
//     {
//         broadcast use PteFlags::lemma_each_bits_is_valid;
//         let flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&perm)).0.0);
//         if flags.contains(PRESENT) {
//             return Mapping::Level3(entry, Tracked(perm));
//         }
//         let (page, Tracked(mut page_perm)) = {
//             let (page, page_perm) = Box::<Page>::new_zeroed(&DEKO_FRAME_ALLOCATOR.0);
//             page.into_ptr(page_perm)
//         };
//         let flags = PRESENT | WRITABLE | USER | ACCESSED;
//         let new_pte_value = make_private_address(page.addr() as u64) | flags;
//         let tracked mut perm = perm;
//         entry.write(Tracked(&mut perm), PageTableEntry(PhysAddr(new_pte_value)));
//         let idx = index_at_level::<1>(vaddr);
//         let next_entry = page.addr() + idx * 8;
//         let (next_entry, Tracked(next_entry_perm)) = unsafe {
//             DekoPPtr::<PageTableEntry>::from_raw_init(next_entry as u64)
//         };
//         Page::allocate_pte_level1(next_entry, Tracked(next_entry_perm), vaddr, huge_page)
//     }
//     /// Allocates a page table entry at level 3 (the root level).
//     #[verifier::external_body]
//     fn allocate_pte_level3(
//         entry: DekoPPtr<PageTableEntry>,
//         Tracked(perm): Tracked<DekoPointsTo<PageTableEntry>>,
//         vaddr: VirtAddr,
//         huge_page: bool,
//     ) -> (r: Mapping)
//         requires
//             entry@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//             entry.addr() + 0x1000 <= usize::MAX,
//         ensures
//             r.wf(),
//     {
//         broadcast use PteFlags::lemma_each_bits_is_valid;
//         let flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&perm)).0.0);
//         if flags.contains(PRESENT) {
//             return Mapping::Level3(entry, Tracked(perm));
//         }
//         let (page, Tracked(mut page_perm)) = {
//             let (page, page_perm) = Box::<Page>::new_zeroed(&DEKO_FRAME_ALLOCATOR.0);
//             page.into_ptr(page_perm)
//         };
//         let flags = PRESENT | WRITABLE | USER | ACCESSED;
//         let new_pte_value = make_private_address(page.addr() as u64) | flags;
//         let tracked mut perm = perm;
//         entry.write(Tracked(&mut perm), PageTableEntry(PhysAddr(new_pte_value)));
//         let idx = index_at_level::<2>(vaddr);
//         let next_entry = page.addr() + idx * 8;
//         let (next_entry, Tracked(next_entry_perm)) = unsafe {
//             DekoPPtr::<PageTableEntry>::from_raw_init(next_entry as u64)
//         };
//         Page::allocate_pte_level2(next_entry, Tracked(next_entry_perm), vaddr, huge_page)
//     }
//     /// Allocates a 4KB page table entry for a given virtual address.
//     pub fn alloc_pte_4k(
//         pgtable: DekoPPtr<PageTable>,
//         Tracked(perm): Tracked<DekoPointsTo<Page>>,
//         vaddr: VirtAddr,
//     ) -> (r: Mapping)
//         requires
//             pgtable@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//             pgtable.addr() + 0x1000 <= usize::MAX,
//         ensures
//             r.wf(),
//     {
//         let mapping = PageTable::walk(pgtable, Tracked(perm), vaddr);
//         match mapping {
//             Mapping::Level0(entry, entry_perm) => Mapping::Level0(entry, entry_perm),
//             Mapping::Level1(entry, entry_perm) => Page::allocate_pte_level1(
//                 entry,
//                 entry_perm,
//                 vaddr,
//                 false,
//             ),
//             Mapping::Level2(entry, entry_perm) => Page::allocate_pte_level2(
//                 entry,
//                 entry_perm,
//                 vaddr,
//                 false,
//             ),
//             Mapping::Level3(entry, entry_perm) => Page::allocate_pte_level3(
//                 entry,
//                 entry_perm,
//                 vaddr,
//                 false,
//             ),
//         }
//     }
//     #[verifier::external_body]
//     pub fn do_split_4k(
//         entry: DekoPPtr<PageTableEntry>,
//         Tracked(perm): Tracked<DekoPointsTo<PageTableEntry>>,
//     )
//         requires
//             entry@ == perm.pptr(),
//             perm.is_init(),
//             perm.mem_wf(),
//             perm.wf(),
//             entry.addr() + 0x1000 <= usize::MAX,
//     {
//         let mut flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&perm)).0.0);
//         if !flags.contains(HUGE) {
//             vstd::vpanic!("not a huge page");
//         }
//         // Allocate a new page.
//         let (page, Tracked(mut page_perm)) = {
//             let (page, page_perm) = Box::<Page>::new_zeroed(&DEKO_FRAME_ALLOCATOR.0);
//             page.into_ptr(page_perm)
//         };
//         let paddr = page.addr() as u64;
//         // Get the starting address of the 2M page.
//         let addr_2m = entry.borrow(Tracked(&perm)).address().0 & 0x000f_ffff_fff0_0000;
//         flags.remove(HUGE);
//         // Now populate the new leaf PTE.
//         let mut i = 0u64;
//         while i < PAGE_TABLE_ENTRY as u64
//             invariant
//                 i <= PAGE_TABLE_ENTRY,
//         {
//             // Split this huge page into 512 4K pages.
//             let addr_4k = addr_2m + (i * PAGE_SIZE);
//             let (e, Tracked(mut e_perm)) = unsafe {
//                 // ADD MORE
//                 DekoPPtr::<PageTableEntry>::from_raw_init(page.addr() as u64 + i * 8)
//             };
//             e.write(
//                 Tracked(&mut e_perm),
//                 PageTableEntry(PhysAddr(make_private_address(addr_4k) | flags.bits())),
//             );
//             i += 1;
//         }
//         // Finally, update the original PTE to point to the new page.
//         entry.write(
//             Tracked(&mut perm),
//             PageTableEntry(PhysAddr(make_private_address(paddr) | flags.bits())),
//         );
//         flush_tlb();
//     }
//     pub fn split_4k(mapping: Mapping)
//         requires
//             mapping.wf(),
//     {
//         match mapping {
//             Mapping::Level0(_, _) => {},
//             Mapping::Level1(entry, entry_perm) => {
//                 Page::do_split_4k(entry, entry_perm);
//             },
//             _ => {
//                 vstd::vpanic!("unexpected mapping type");
//             },
//         }
//     }
//     /// Sets the shared state for a 4KB page.
//     #[verifier::external_body]
//     pub fn set_shared_4k(
//         pgtable: DekoPPtr<PageTable>,
//         Tracked(perm): Tracked<DekoPointsTo<Page>>,
//         vaddr: VirtAddr,
//     ) {
//         // Should return a Level 1 mapping due to huge page.
//         let mapping = PageTable::walk(pgtable, Tracked(perm), vaddr);
//         PageTable::split_4k(mapping);
//         // walk again to obtain the level 0 mapping.
//         let mapping = PageTable::walk(pgtable, Tracked(perm), vaddr);
//         match mapping {
//             Mapping::Level0(entry, entry_perm) => {
//                 let Tracked(mut entry_perm) = entry_perm;
//                 let flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&entry_perm)).0.0);
//                 let addr = entry.borrow(Tracked(&entry_perm)).address();
//                 let addr = make_shared_address(addr.0);
//                 entry.write(
//                     Tracked(&mut entry_perm),
//                     PageTableEntry(PhysAddr(addr | flags.bits())),
//                 );
//             },
//             _ => {
//                 vstd::vpanic!("unexpected mapping type");
//             },
//         }
//         flush_tlb();
//     }
//     /// Maps a single page at the given virtual address to the given physical address
//     /// with the given flags.
//     #[verifier::external_body]
//     pub fn map_page_4k(
//         pgtable: DekoPPtr<PageTable>,
//         Tracked(perm): Tracked<&mut PageTablePermission>,
//         vaddr: VirtAddr,
//         paddr: PhysAddr,
//         flags: PteFlags,
//     ) {
//         let mapping = Page::alloc_pte_4k(pgtable, Tracked(perm), vaddr);
//         match mapping {
//             Mapping::Level0(entry, entry_perm) => {
//                 let Tracked(mut entry_perm) = entry_perm;
//                 let new_pte_value = make_private_address(paddr.0) | flags.bits();
//                 entry.write(Tracked(&mut entry_perm), PageTableEntry(PhysAddr(new_pte_value)));
//             },
//             _ => {
//                 vstd::vpanic!("unexpected mapping type");
//             },
//         }
//     }
//     closed spec fn get_pte_address_spec(vaddr: VirtAddr) -> VirtAddr
//         recommends
//             vaddr@ < 0x0000_8000_0000_0000,
//     {
//         VirtAddr((PTE_BASE.0 + ((vaddr.0 & 0x0000_FFFF_FFFF_F000) >> 9)) as u64)
//     }
//     /// Extracts the virtual address of the PTE that maps the given virtual address `vaddr`.
//     #[verifier::external_body]
//     #[verifier::when_used_as_spec(get_pte_address_spec)]
//     fn get_pte_address(vaddr: VirtAddr) -> (r: VirtAddr)
//         requires
//             vaddr.wf(),
//         ensures
//             r == Self::get_pte_address_spec(vaddr),
//             r.wf(),
//     {
//         VirtAddr(PTE_BASE.0 + ((vaddr.0 & 0x0000_FFFF_FFFF_F000) >> 9))
//     }
//     pub open spec fn virt_to_frame_spec(vaddr: VirtAddr) -> Option<PageFrame> {
//         None
//     }
//     #[verifier::when_used_as_spec(virt_to_frame_spec)]
//     #[verifier::external_body]
//     pub fn virt_to_frame(vaddr: VirtAddr) -> (r: Option<PageFrame>)
//         requires
//             vaddr.wf(),
//         ensures
//             r == Self::virt_to_frame_spec(vaddr),
//     {
//         broadcast use PteFlags::lemma_each_bits_is_valid;
//         // Calculate the virtual addresses of each level of the paging
//         // hierarchy in the self-map.
//         let pte_addr = Self::get_pte_address(vaddr);
//         let pde_addr = Self::get_pte_address(pte_addr);
//         let pdpe_addr = Self::get_pte_address(pde_addr);
//         let pml4e_addr = Self::get_pte_address(pdpe_addr);
//         let (pml4e, Tracked(pml4e_perm)) = unsafe {
//             DekoPPtr::<PageTableEntry>::from_raw_init(pml4e_addr.0)
//         };
//         let pml4e_flags = PteFlags::from_bits_truncate(pml4e.borrow(Tracked(&pml4e_perm)).0.0);
//         if !pml4e_flags.contains(PRESENT) {
//             return None;
//         }
//         let (pdpe, Tracked(pdpe_perm)) = unsafe {
//             DekoPPtr::<PageTableEntry>::from_raw_init(pdpe_addr.0)
//         };
//         let pdpe_flags = PteFlags::from_bits_truncate(pdpe.borrow(Tracked(&pdpe_perm)).0.0);
//         if !pdpe_flags.contains(PRESENT) {
//             return None;
//         }
//         if pdpe_flags.contains(HUGE) {
//             return Some(
//                 PageFrame::Frame1G(
//                     PhysAddr(
//                         pdpe.borrow(Tracked(&pdpe_perm)).address().0 + (vaddr.0 & 0x001F_FFFF),
//                     ),
//                 ),
//             );
//         }
//         let (pde, Tracked(pde_perm)) = unsafe {
//             DekoPPtr::<PageTableEntry>::from_raw_init(pde_addr.0)
//         };
//         let pde_flags = PteFlags::from_bits_truncate(pde.borrow(Tracked(&pde_perm)).0.0);
//         if !pde_flags.contains(PRESENT) {
//             return None;
//         }
//         if pde_flags.contains(HUGE) {
//             return Some(
//                 PageFrame::Frame2M(
//                     PhysAddr(pde.borrow(Tracked(&pde_perm)).address().0 + (vaddr.0 & 0x000F_FFFF)),
//                 ),
//             );
//         }
//         let (pte, Tracked(pte_perm)) = unsafe {
//             DekoPPtr::<PageTableEntry>::from_raw_init(pte_addr.0)
//         };
//         let pte_flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&pte_perm)).0.0);
//         if !pte_flags.contains(PRESENT) {
//             return None;
//         }
//         Some(
//             PageFrame::Frame4K(
//                 PhysAddr(pte.borrow(Tracked(&pte_perm)).address().0 + (vaddr.0 & 0x0000_0FFF)),
//             ),
//         )
//     }
// }
// #[verifier::external_body]
// #[inline(always)]
// pub fn get_initial_pgtable() -> (r: (DekoPPtr<PageTable>, Tracked<DekoPointsTo<PageTable>>))
//     ensures
//         r.0@ === r.1@.pptr(),
//         r.1.wf(),
//         r.1@.is_init(),
// {
//     unsafe {
//         DekoPPtr::from_raw_init(
//             (core::ptr::addr_of!(initial_page_table) as *const PageTable) as u64,
//         )
//     }
// }
// } // verus!
// Re-export PTE_BASE from deko-std for backward compatibility
pub use deko_std::address::PTE_BASE;
use vstd::prelude::*;

use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::DekoCpuCtx;
use crate::prelude::*;

deko_bitflags! {
    pub struct Pte: u64 {
        const PRESENT       = 0;
        const WRITABLE      = 1;
        const USER          = 2;
        // const PWT           = 3;
        // const PCD           = 4;
        const ACCESSED      = 5;
        const DIRTY         = 6;
        const HUGE          = 7;
        const GLOBAL        = 8;
        const NX            = 63;
    }
}

verus! {

#[verifier::inline]
pub open spec fn strip_confidentiality_bits_spec(paddr: u64, private_bit: u64) -> u64 {
    paddr & !private_bit
}

#[verifier::inline]
pub open spec fn strip_shared_address_bits_spec(paddr: u64, shared_bit: u64) -> u64 {
    paddr & !shared_bit
}

#[verifier::inline]
pub open spec fn make_private_address_spec(paddr: u64, private_bit: u64, shared_bit: u64) -> u64 {
    strip_shared_address_bits_spec(paddr, shared_bit) | private_bit
}

#[verifier::inline]
pub open spec fn make_shared_address_spec(paddr: u64, private_bit: u64, shared_bit: u64) -> u64 {
    strip_confidentiality_bits_spec(paddr, private_bit) | shared_bit
}

#[verifier::when_used_as_spec(strip_confidentiality_bits_spec)]
pub fn strip_confidentiality_bits(paddr: u64, private_bit: u64) -> (r: u64)
    ensures
        r == strip_confidentiality_bits_spec(paddr, private_bit),
{
    paddr & !private_bit
}

#[verifier::when_used_as_spec(strip_shared_address_bits_spec)]
pub fn strip_shared_address_bits(paddr: u64, shared_bit: u64) -> (r: u64)
    ensures
        r == strip_shared_address_bits_spec(paddr, shared_bit),
{
    paddr & !shared_bit
}

#[verifier::when_used_as_spec(make_private_address_spec)]
pub fn make_private_address(paddr: u64, private_bit: u64, shared_bit: u64) -> (r: u64)
    ensures
        r == make_private_address_spec(paddr, private_bit, shared_bit),
{
    strip_shared_address_bits(paddr, shared_bit) | private_bit
}

#[verifier::when_used_as_spec(make_shared_address_spec)]
pub fn make_shared_address(paddr: u64, private_bit: u64, shared_bit: u64) -> (r: u64)
    ensures
        r == make_shared_address_spec(paddr, private_bit, shared_bit),
{
    strip_confidentiality_bits(paddr, private_bit) | shared_bit
}

/// Defines a common trait for page table entries.
pub trait PteBehavior: WellFormed + View<V = PhysAddr> {
    spec fn is_valid_pte_spec(&self) -> bool;

    spec fn is_huge_pte_spec(&self) -> bool;

    spec fn is_present_pte_spec(&self) -> bool;

    spec fn address_spec(&self, private_bit: u64, shared_bit: u64) -> (r: PhysAddr);

    /// Get the address from the page table entry, including the shared bit.
    fn page_frame(&self, private_bit: u64) -> (r: PhysAddr)
        requires
            self.wf(),
        ensures
            r.wf(),
    // r@ == Self::strip_confidentiality_bits_spec(self@@ & 0x000f_ffff_ffff_f000),

    ;

    /// Get the address from the page table entry, excluding the C/shared bit.
    #[verifier::when_used_as_spec(address_spec)]
    fn address(&self, private_bit: u64, shared_bit: u64) -> (r: PhysAddr)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == self.address_spec(private_bit, shared_bit),
    ;

    /// This function checks whether a given PTE is valid in the sense that
    /// it is either not present, or it is huge page so that we will need to
    /// take extra care when handling it.
    fn is_valid_pte(pte: DekoPPtr<Self>, Tracked(perm): Tracked<&DekoPointsTo<Self>>) -> (r: bool)
        requires
            pte@ == perm.pptr(),
            perm.is_init(),
            perm.wf(),
        ensures
            r == Self::is_valid_pte_spec(&perm.value()),
    ;

    fn is_huge_pte(pte: DekoPPtr<Self>, Tracked(perm): Tracked<&DekoPointsTo<Self>>) -> (r: bool)
        requires
            pte@ == perm.pptr(),
            perm.is_init(),
            perm.wf(),
        ensures
            r == Self::is_huge_pte_spec(&perm.value()),
    ;

    fn is_present_pte(pte: DekoPPtr<Self>, Tracked(perm): Tracked<&DekoPointsTo<Self>>) -> (r: bool)
        requires
            pte@ == perm.pptr(),
            perm.is_init(),
            perm.wf(),
        ensures
            r == Self::is_present_pte_spec(&perm.value()),
    ;
}

/// Defines a common trait for page table behaviors.
///
/// TODO: Design specs later.
pub trait PageTableBehavior: WellFormed {
    /// Converts a virtual address to a page frame if it is mapped.
    fn virt_to_frame(vaddr: VirtAddr) -> (r: PageFrame);

    /// Walks the page table to find the page table entry for a given virtual address.
    fn walk(
        pgtable: DekoPPtr<Self>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: DekoPagePtr);

    /// Sets a given page as shared.
    fn set_shared_4k(
        pgtable: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    );

    /// Maps a single 4KB page at the given virtual address to the given physical address
    fn map_page_4k(
        pgtable: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PteFlags,
        private_bit: u64,
        shared_bit: u64,
    );
}

/// This function calculates the index at a given level L in the 4-level page table
/// hierarchy for a given virtual address `vaddr`.
#[inline]
pub fn index_at_level<const L: usize>(vaddr: VirtAddr) -> (r: usize)
    requires
        L < 4,
    ensures
        r < PAGE_TABLE_ENTRY,
{
    proof {
        assert forall|n: u64| n & 0x1ff < PAGE_TABLE_ENTRY by {
            bit_u64_and_auto();
        }
    }
    ((vaddr.0 >> (12 + L * 9)) & 0x1ff) as usize
}

/// Specification version of index_at_level for use in specs
pub open spec fn index_at_level_spec(level: nat, vaddr: VirtAddr) -> nat
    recommends
        level < 4,
{
    ((vaddr.0 >> (12 + level * 9)) & 0x1ff) as nat
}

pub open spec fn phys_to_virt_spec(ms: MappingSpace, paddr: PhysAddr) -> VirtAddr
    recommends
        ms.physmap.in_range_spec(paddr) || ms.kernel.in_range_spec(paddr),
{
    if ms.kernel.in_range_spec(paddr) {
        ms.kernel.phys_to_virt_spec(paddr)
    } else {
        ms.physmap.phys_to_virt_spec(paddr)
    }
}

/// Converts a physical address to a virtual address using the provided context's mapping space.
#[inline(always)]
pub fn phys_to_virt(
    ctx: DekoPPtr<DekoCtx>,
    Tracked(ctx_perm): Tracked<&DekoCtxPermission>,
    paddr: PhysAddr,
) -> (vaddr: VirtAddr)
    requires
        paddr.wf(),
        ctx_perm.wf_with(ctx),
        ctx_perm.in_heap_range(paddr),
    ensures
        vaddr.wf(),
        vaddr == phys_to_virt_spec(ctx_perm.mapping_space, paddr),
{
    let ms = ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).mapping_space;

    ms.phys_to_virt(paddr)
}

deko_bitflags_quick! {
    Pte,
    data: { PRESENT, WRITABLE, USER, ACCESSED, DIRTY, GLOBAL, NX },
    writeable: { PRESENT, USER, WRITABLE, ACCESSED, DIRTY },
    read_only: { PRESENT, USER, ACCESSED },
    kernel_code: { PRESENT, GLOBAL },
}

/// Another wrapper over DekoPPtr for handling page tables.
#[repr(C, align(8))]
pub struct DekoPagePtr(pub DekoPPtr<Page>);

/// A page table entry that is backed by a physical address.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct PageTableEntry(pub PhysAddr);

/// This struct contains a 4KiB array. Be careful when passing it around
/// as it might overflow the stack. The user should, at all times, pass
/// around a pointer to it instead of the struct itself.
#[repr(C)]
pub struct Page(pub Array<PageTableEntry, PAGE_TABLE_ENTRY>);

/// Used to index into the page table permission map [`PageTablePermission`].
/// (level, index)
pub type PagePermissionIndex = (nat, int);

#[allow(inconsistent_fields)]
pub tracked enum PagePermission {
    Level0 { idx: nat, value: PageTableEntry, this_page_perm: DekoPointsTo<Page> },
    LevelN {
        level: nat,  // 1, 2, or 3
        idx: int,
        value: PageTableEntry,
        this_page_perm: DekoPointsTo<Page>,
        next_page_perm: DekoPointsTo<Page>,
    },
}

with_permission! {
    PageTable,
    pgtable_perm: DekoPointsTo<PageTable>, // root permission.
    storage: Map<PagePermissionIndex, PagePermission>,
    private_bit: u64,
    shared_bit: u64,
}

impl WellFormed for PageTablePermission {
    open spec fn wf(&self) -> bool {
        &&& self.pgtable_perm.is_init() && self.pgtable_perm.wf()
        &&& self.wf_with_perm()
    }
}

impl WellFormed for PageTableEntry {
    // This needs to be stronger:
    //
    // a PTE might be convertible into a Page so that
    // we must at least guarantee that for non-leaf
    // PTEs, the page conversion should succeed.
    //
    // HACK: For now we just assume everything.
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        self.0.wf()
    }
}

impl View for PageTableEntry {
    type V = PhysAddr;

    #[verifier::inline]
    open spec fn view(&self) -> PhysAddr {
        self.0
    }
}

impl WellFormed for Page {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        self.0.wf()
    }
}

impl View for Page {
    type V = PhysAddr;

    uninterp spec fn view(&self) -> Self::V;
}

impl WellFormed for PageFrame {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        match self {
            PageFrame::Frame4K(paddr) => paddr.wf(),
            PageFrame::Frame2M(paddr) => paddr.wf(),
            PageFrame::Frame1G(paddr) => paddr.wf(),
        }
    }
}

impl PageFrame {
    /// Get the address from the page frame, including the shared bit.
    pub fn page_frame(&self, private_bit: u64) -> (r: PhysAddr) {
        let paddr = match *self {
            Self::Frame4K(pa) => pa,
            Self::Frame2M(pa) => pa,
            Self::Frame1G(pa) => pa,
        };
        PhysAddr(strip_confidentiality_bits(paddr.0, private_bit))
    }

    /// Get the address from the page frame, excluding the C/shared bit.
    pub fn address(&self, private_bit: u64, shared_bit: u64) -> (r: PhysAddr) {
        PhysAddr(strip_shared_address_bits(self.page_frame(private_bit).0, shared_bit))
    }
}

impl Page {
    pub uninterp spec fn level(&self) -> nat;
}

impl PageTablePermission {
    /// Ensures all PTEs are within the valid physical range.
    pub open spec fn pte_within_range(&self, start_phys: u64, end_phys: u64) -> bool {
        &&& forall|i: (PagePermissionIndex, PagePermission)|
            self.storage.contains_key(i.0) ==> {
                let pte = match i.1 {
                    PagePermission::Level0 { value, .. } => value,
                    PagePermission::LevelN { value, .. } => value,
                };
                let paddr = pte.address_spec(self.private_bit, self.shared_bit);
                start_phys <= paddr@ < end_phys
            }
    }

    /// Updates the permission structure when a new page table entry is added
    /// This maintains the mirror property by ensuring the storage map reflects
    /// the actual page table structure
    pub open spec fn update_entry(&self, level: nat, idx: int, new_entry: PagePermission) -> Self
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
            new_entry.level() == level,
            new_entry.idx() == idx,
    {
        PageTablePermission {
            pgtable_perm: self.pgtable_perm,
            // If the key is already present from the map,
            // then its existing value is overwritten by the new value.
            storage: self.storage.insert((level, idx), new_entry),
            private_bit: self.private_bit,
            shared_bit: self.shared_bit,
        }
    }

    /// Removes an entry from the permission structure
    /// Used when a page table entry is deallocated or becomes invalid
    pub open spec fn remove_entry(&self, level: nat, idx: int) -> Self
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
    {
        PageTablePermission {
            pgtable_perm: self.pgtable_perm,
            storage: self.storage.remove((level, idx)),
            private_bit: self.private_bit,
            shared_bit: self.shared_bit,
        }
    }

    /// Adds an entry to the permission structure only if it represents a present PTE
    /// This maintains the mirror property by only tracking present entries
    pub open spec fn add_present_entry(
        &self,
        level: nat,
        idx: int,
        new_entry: PagePermission,
    ) -> Self
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
            new_entry.level() == level,
            new_entry.idx() == idx,
            new_entry.wf(),
    {
        PageTablePermission {
            pgtable_perm: self.pgtable_perm,
            storage: self.storage.insert((level, idx), new_entry),
            private_bit: self.private_bit,
            shared_bit: self.shared_bit,
        }
    }

    /// Removes an entry when it becomes non-present
    /// This maintains the mirror property by removing non-present entries
    pub open spec fn remove_non_present_entry(&self, level: nat, idx: int) -> Self
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
    {
        PageTablePermission {
            pgtable_perm: self.pgtable_perm,
            storage: self.storage.remove((level, idx)),
            private_bit: self.private_bit,
            shared_bit: self.shared_bit,
        }
    }

    /// Updates an entry's presence status - adds if present, removes if not present
    pub open spec fn update_entry_presence(
        &self,
        level: nat,
        idx: int,
        new_entry: Option<PagePermission>,
    ) -> Self
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
            new_entry matches Some(entry) ==> (entry.level() == level && entry.idx() == idx
                && entry.wf()),
    {
        match new_entry {
            Some(entry) => self.add_present_entry(level, idx, entry),
            None => self.remove_non_present_entry(level, idx),
        }
    }

    /// Creates a new PageTablePermission with an empty storage map
    /// Used when initializing a new page table
    pub open spec fn empty(root_perm: DekoPointsTo<PageTable>) -> Self {
        PageTablePermission {
            pgtable_perm: root_perm,
            storage: Map::empty(),
            private_bit: 0,
            shared_bit: 0,
        }
    }

    /// Validates that a page table modification preserves the mirror property
    /// Only allows updates for present entries
    pub open spec fn can_update_entry(
        &self,
        level: nat,
        idx: int,
        new_entry: PagePermission,
    ) -> bool
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
    {
        &&& new_entry.wf()
        &&& new_entry.level() == level
        &&& new_entry.idx() == idx
        // Entry must represent a present PTE
        &&& self.entry_is_present(
            level,
            idx,
            new_entry,
        )
        // Ensure the update maintains consistency with parent/child relationships
        &&& match level as u64 {
            4 => {
                // Root level - should point to initial page table (always present)
                new_entry.value().0@ == initial_page_table_value()
            },
            _ => {
                // For non-root levels, ensure proper nesting
                match new_entry.next_page_perm() {
                    Some(next) => next.value().level() == level - 1,
                    None => level == 0  // Only leaf entries can have None
                    ,
                }
            },
        }
    }

    /// Validates that a page table entry can be removed (made non-present)
    pub open spec fn can_remove_entry(&self, level: nat, idx: int) -> bool
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
    {
        // Can only remove entries that are currently present in storage
        &&& self.storage.contains_key(
            (level, idx),
        )
        // Root entry (level 4, idx 0) should never be removed as it's always present
        &&& !(level == 4 && idx == 0)
    }

    /// This is a recursive specification that checks if the storage map
    /// correctly mirrors the actual page table structure down to level `lvl`.
    ///
    /// The mirror property ensures that:
    /// 1. Only present entries are tracked in the storage map
    /// 2. Each tracked entry's physical address matches what's stored in the actual page table
    /// 3. The hierarchy is consistent (parent entries point to child page tables)
    /// 4. Leaf entries (level 0) don't have next_page_perm
    /// 5. Non-present entries are not tracked in the storage map
    pub open spec fn mirrors(&self, lvl: nat) -> bool
        recommends
            0 <= lvl <= 4,
        decreases lvl,
    {
        match lvl as u64 {
            4 => {
                // For the root page table (level 4), we check that:
                // 1. The root entry exists and is well-formed (root is always present)
                // 2. It corresponds to the actual root page table
                &&& self.storage.contains_key((4, 0))
                &&& {
                    let root = self.storage[(4, 0)];
                    &&& root.wf()
                    &&& root.level() == 4 && root.idx() == 0
                    &&& root.this_page_perm().is_init()
                    // The root should point to the initial page table
                    &&& root.value().0@
                        == initial_page_table_value()
                    // Root is always present
                    &&& self.entry_is_present(4, 0, root)
                }
                // Recursively check level 3
                &&& self.mirrors(3)
            },
            3 => {
                // For level 3 (PML4 entries), only track present entries
                &&& forall|idx: int|
                    0 <= idx < PAGE_TABLE_ENTRY as int ==> {
                        // If an entry is in storage, it must be present and well-formed
                        self.storage.contains_key((3, idx)) ==> {
                            let entry = self.storage[(3, idx)];
                            &&& entry.wf()
                            &&& entry.level() == 3 && entry.idx() == idx
                            &&& entry.this_page_perm().is_init()
                            // Entry must represent a present PTE
                            &&& self.entry_is_present(
                                3,
                                idx,
                                entry,
                            )
                            // If this entry points to a next level page table,
                            // then next_page_perm should be Some and well-formed
                            &&& match entry.next_page_perm() {
                                Some(next_perm) => {
                                    &&& next_perm.wf()
                                    // &&& next_perm.level() == 2
                                    // The physical address should match
                                    &&& next_perm.value()@ == entry.value()@
                                },
                                None => true  // Leaf entry (huge page)
                                ,
                            }
                        }
                    }
                    // Recursively check level 2
                &&& self.mirrors(2)
            },
            2 => {
                // For level 2 (PDPT entries), only track present entries
                &&& forall|idx: int|
                    0 <= idx < PAGE_TABLE_ENTRY as int ==> {
                        self.storage.contains_key((2, idx)) ==> {
                            let entry = self.storage[(2, idx)];
                            &&& entry.wf()
                            &&& entry.level() == 2 && entry.idx() == idx
                            &&& entry.this_page_perm().is_init()
                            // Entry must represent a present PTE
                            &&& self.entry_is_present(2, idx, entry)
                            &&& match entry.next_page_perm() {
                                Some(next_perm) => {
                                    &&& next_perm.wf()
                                    // &&& next_perm.level() == 1
                                    &&& next_perm.value()@ == entry.value()@
                                },
                                None => true  // Huge page
                                ,
                            }
                        }
                    }
                    // Recursively check level 1
                &&& self.mirrors(1)
            },
            1 => {
                // For level 1 (PD entries), only track present entries
                &&& forall|idx: int|
                    0 <= idx < PAGE_TABLE_ENTRY as int ==> {
                        self.storage.contains_key((1, idx)) ==> {
                            let entry = self.storage[(1, idx)];
                            &&& entry.wf()
                            &&& entry.level() == 1 && entry.idx() == idx
                            &&& entry.this_page_perm().is_init()
                            // Entry must represent a present PTE
                            &&& self.entry_is_present(1, idx, entry)
                            &&& match entry.next_page_perm() {
                                Some(next_perm) => {
                                    &&& next_perm.wf()
                                    // &&& next_perm.level() == 0
                                    &&& next_perm.value()@ == entry.value()@
                                },
                                None => true  // Huge page
                                ,
                            }
                        }
                    }
                    // Recursively check level 0
                &&& self.mirrors(0)
            },
            0 => {
                // For level 0 (PT entries - leaf level), only track present entries
                &&& forall|idx: int|
                    0 <= idx < PAGE_TABLE_ENTRY as int ==> {
                        self.storage.contains_key((0, idx)) ==> {
                            let entry = self.storage[(0, idx)];
                            &&& entry.wf()
                            &&& entry.level() == 0 && entry.idx() == idx
                            &&& entry.this_page_perm().is_init()
                            // Entry must represent a present PTE
                            &&& self.entry_is_present(
                                0,
                                idx,
                                entry,
                            )
                            // Level 0 entries should never have next_page_perm
                            &&& entry.next_page_perm() matches None
                        }
                    }
            },
            _ => false  // Invalid level
            ,
        }
    }

    /// Helper function to check if an entry represents a present page table entry
    /// This checks that the PRESENT bit is set in the corresponding PTE
    pub open spec fn entry_is_present(&self, level: nat, idx: int, entry: PagePermission) -> bool
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
    {
        // Check the PRESENT bit in the PageTableEntry using the is_present_spec function
        entry.value().is_present_pte_spec()
    }

    // This specification says that for every entry in the storage map,
    // it must be well-formed and match its (level, index) key.
    // Only present entries are required to be in the storage map.
    //
    // This ensures the storage mirrors only the present entries in the actual page table structure.
    pub open spec fn wf_with_perm(&self) -> bool {
        self.mirrors(4)
    }
}

impl PagePermission {
    pub open spec fn level(&self) -> nat {
        match self {
            PagePermission::Level0 { .. } => 0,
            PagePermission::LevelN { level, .. } => *level,
        }
    }

    pub open spec fn idx(&self) -> int {
        match self {
            PagePermission::Level0 { idx, .. } => *idx as int,
            PagePermission::LevelN { idx, .. } => *idx,
        }
    }

    pub open spec fn value(&self) -> PageTableEntry {
        match self {
            PagePermission::Level0 { value, .. } => *value,
            PagePermission::LevelN { value, .. } => *value,
        }
    }

    pub open spec fn this_page_perm(&self) -> DekoPointsTo<Page> {
        match self {
            PagePermission::Level0 { this_page_perm, .. } => *this_page_perm,
            PagePermission::LevelN { this_page_perm, .. } => *this_page_perm,
        }
    }

    pub open spec fn next_page_perm(&self) -> Option<DekoPointsTo<Page>> {
        match self {
            PagePermission::Level0 { .. } => None,
            PagePermission::LevelN { next_page_perm, .. } => Some(*next_page_perm),
        }
    }

    pub open spec fn wf_level(&self) -> bool {
        &&& self.level() <= 4  // must be a valid level
        &&& self.this_page_perm().is_init() && self.this_page_perm().wf()
        &&& { self.level() == 0 <==> self.next_page_perm() matches None }
        &&& { self.level() > 0 <==> { self.next_page_perm() matches Some(pg) ==> pg.wf() } }
        &&& match self {
            PagePermission::Level0 { idx, .. } => 0 <= *idx < PAGE_TABLE_ENTRY,
            PagePermission::LevelN { level, idx, .. } => {
                &&& 1 <= *level <= 3
                &&& 0 <= *idx < PAGE_TABLE_ENTRY as int
            },
        }
    }
}

impl View for PageTablePermission {
    type V = Map<PagePermissionIndex, PagePermission>;

    closed spec fn view(&self) -> Self::V {
        self.storage
    }
}

impl WellFormed for PagePermission {
    open spec fn wf(&self) -> bool {
        &&& self.wf_level()
    }
}

/// An alias to [`Page`] to indicate that it is a root page table (conceptually).
pub type PageTable = Page;

/// A page frame.
pub enum PageFrame {
    Frame4K(PhysAddr),
    Frame2M(PhysAddr),
    Frame1G(PhysAddr),
}

/// A mapping at a specific level in the page table hierarchy.
///
/// Please note that the _wrapper_ pointer is the _virtual_address_ of the
/// corresponding PTEs at that level.
///
/// We don't define specs or proofs on this type because eventually
/// the reasoning is based on `PageTableEntry` and `PagePermissionIndex`.
pub enum Mapping {
    Level3(DekoPPtr<PageTableEntry>, Tracked<PagePermissionIndex>),
    Level2(DekoPPtr<PageTableEntry>, Tracked<PagePermissionIndex>),
    Level1(DekoPPtr<PageTableEntry>, Tracked<PagePermissionIndex>),
    Level0(DekoPPtr<PageTableEntry>, Tracked<PagePermissionIndex>),
}

// PageTableEntry can be safely cast into a Page when it represents a valid, present,
// non-huge page table entry that points to a properly aligned page table.
impl SafeCastInto<Page> for PageTableEntry {
    #[verifier::inline]
    open spec fn cast_valid(&self) -> bool {
        &&& self.is_present_pte_spec()  // Must be present
        &&& !self.is_huge_pte_spec()  // Must not be a huge page (leaf entry)

    }

    uninterp spec fn cast_into(from: Self) -> Page;
}

// Auto implementation
impl WellFormed for Mapping {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        match self {
            Mapping::Level3(pte, idx) => idx@.0 == 3 && 0 <= idx@.1 < PAGE_TABLE_ENTRY as int,
            Mapping::Level2(pte, idx) => idx@.0 == 2 && 0 <= idx@.1 < PAGE_TABLE_ENTRY as int,
            Mapping::Level1(pte, idx) => idx@.0 == 1 && 0 <= idx@.1 < PAGE_TABLE_ENTRY as int,
            Mapping::Level0(pte, idx) => idx@.0 == 0 && 0 <= idx@.1 < PAGE_TABLE_ENTRY as int,
        }
    }
}

impl View for Mapping {
    type V = (DekoPPtr<PageTableEntry>, Tracked<PagePermissionIndex>);

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        self.into_inner_spec()
    }
}

impl Mapping {
    pub open spec fn into_inner_spec(&self) -> (
        DekoPPtr<PageTableEntry>,
        Tracked<PagePermissionIndex>,
    ) {
        match self {
            Mapping::Level3(pte, idx) => (*pte, *idx),
            Mapping::Level2(pte, idx) => (*pte, *idx),
            Mapping::Level1(pte, idx) => (*pte, *idx),
            Mapping::Level0(pte, idx) => (*pte, *idx),
        }
    }

    #[verifier::inline]
    pub open spec fn level_spec(&self) -> usize {
        match self {
            Mapping::Level3(_, _) => 3,
            Mapping::Level2(_, _) => 2,
            Mapping::Level1(_, _) => 1,
            Mapping::Level0(_, _) => 0,
        }
    }

    #[verifier::when_used_as_spec(level_spec)]
    pub fn level(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.level_spec(),
    {
        match self {
            Mapping::Level3(_, _) => 3,
            Mapping::Level2(_, _) => 2,
            Mapping::Level1(_, _) => 1,
            Mapping::Level0(_, _) => 0,
        }
    }
}

impl PteBehavior for PageTableEntry {
    open spec fn address_spec(&self, private_bit: u64, shared_bit: u64) -> PhysAddr {
        PhysAddr(
            strip_shared_address_bits_spec(
                strip_confidentiality_bits_spec(self.0.0 & 0x000f_ffff_ffff_f000, private_bit),
                shared_bit,
            ),
        )
    }

    #[inline]
    fn page_frame(&self, private_bit: u64) -> PhysAddr {
        PhysAddr(strip_confidentiality_bits(self.0.0 & 0x000f_ffff_ffff_f000, private_bit))
    }

    /// Get the address from the page table entry, excluding the C/shared bit.
    #[inline]
    fn address(&self, private_bit: u64, shared_bit: u64) -> PhysAddr {
        PhysAddr(strip_shared_address_bits(self.page_frame(private_bit).0, shared_bit))
    }

    open spec fn is_valid_pte_spec(&self) -> bool {
        let bits = from_bits(self@.0);
        bits.contains(Pte::PRESENT) && !bits.contains(Pte::HUGE)
    }

    open spec fn is_huge_pte_spec(&self) -> bool {
        let bits = from_bits(self@.0);
        bits.contains(Pte::HUGE)
    }

    open spec fn is_present_pte_spec(&self) -> bool {
        let bits = from_bits(self@.0);
        bits.contains(Pte::PRESENT)
    }

    fn is_present_pte(
        pte: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<&DekoPointsTo<PageTableEntry>>,
    ) -> (r: bool)
        ensures
            r == Self::is_present_pte_spec(&perm.value()),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;

        let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
        flags.contains(PRESENT)
    }

    /// This function checks whether a given PTE is valid in the sense that
    /// it is either not present, or it is huge page so that we will need to
    /// take extra care when handling it.
    fn is_valid_pte(
        pte: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<&DekoPointsTo<PageTableEntry>>,
    ) -> (r: bool)
        ensures
            r == Self::is_valid_pte_spec(&perm.value()),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;

        let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
        flags.contains(PRESENT) && !flags.contains(HUGE)
    }

    fn is_huge_pte(
        pte: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<&DekoPointsTo<PageTableEntry>>,
    ) -> (r: bool)
        ensures
            r == Self::is_huge_pte_spec(&perm.value()),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;

        let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
        flags.contains(HUGE)
    }
}

impl PageTableBehavior for PageTable {
    fn virt_to_frame(vaddr: VirtAddr) -> (r: PageFrame) {
        vstd::vpanic!("implement me");
    }

    fn walk(
        pgtable: DekoPPtr<PageTable>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: DekoPagePtr) {
        vstd::vpanic!("implement me");
    }

    fn set_shared_4k(
        pgtable: DekoPPtr<PageTable>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) {
        // // Should return a Level 1 mapping due to huge page.
        // let mapping = PageTable::walk(pgtable, Tracked(perm), vaddr, private_bit, shared_bit);
        // PageTable::split_4k(mapping);
        // // walk again to obtain the level 0 mapping.
        // let mapping = PageTable::walk(pgtable, Tracked(perm), vaddr, private_bit, shared_bit);
        // match mapping {
        //     Mapping::Level0(entry, entry_perm) => {
        //         let Tracked(mut entry_perm) = entry_perm;
        //         let flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&entry_perm)).0.0);
        //         let addr = entry.borrow(Tracked(&entry_perm)).address();
        //         let addr = make_shared_address(addr.0, private_bit, shared_bit);
        //         entry.write(
        //             Tracked(&mut entry_perm),
        //             PageTableEntry(PhysAddr(addr | flags.bits())),
        //         );
        //     },
        //     _ => {
        //         vstd::vpanic!("unexpected mapping type");
        //     },
        // }
        // flush_tlb();
    }

    fn map_page_4k(
        pgtable: DekoPPtr<PageTable>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PteFlags,
        private_bit: u64,
        shared_bit: u64,
    ) {
        vstd::vpanic!("implement me");
    }
}

impl View for DekoPagePtr {
    type V = DekoPPtr<Page>;

    open spec fn view(&self) -> DekoPPtr<Page> {
        self.0
    }
}

impl DekoPagePtr {
    /// Create a `DekoPagePtr` from a valid page table entry so we can access the
    /// page table it points to. Note that since PTE contains the physical address
    /// of the page table; to access the page table it points to, we need to convert
    /// the physical address to a virtual address first.
    pub closed spec fn from_pte_spec<T: PteBehavior>(
        pte: T,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Self) {
        let val = strip_shared_address_bits_spec(
            strip_confidentiality_bits_spec(pte@@ & 0x000f_ffff_ffff_f000, private_bit),
            shared_bit,
        );

        // TODO: Add phys to addr here.

        DekoPagePtr(DekoPPtr(vstd::simple_pptr::PPtr(val as usize, core::marker::PhantomData)))
    }

    #[inline]
    pub fn from_pte(
        ctx: DekoPPtr<DekoCtx>,
        Tracked(ctx_perm): Tracked<&DekoCtxPermission>,
        pte: PageTableEntry,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Self)
        requires
            ctx_perm.wf_with(ctx),
            pte.wf(),
            pte.is_valid_pte_spec(),
        ensures
            r == Self::from_pte_spec(pte, private_bit, shared_bit),
    {
        let paddr = pte.address(private_bit, shared_bit);

        DekoPagePtr(DekoPPtr(vstd::simple_pptr::PPtr(paddr.0 as usize, core::marker::PhantomData)))
    }
}

} // verus!
