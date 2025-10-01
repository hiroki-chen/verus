# Page Table

Paging is the a memory management mechanism that translates virtual addresses used by software into physical addresses used by the hardware.

These page tables are data structures that reside in physical memory. The OS kernel needs to constantly read and modify them, for example, when mapping new memory for a process or handling a page fault. This poses a challenge: how can the kernel, which operates on virtual addresses, conveniently and efficiently access these page table structures that exist in physical memory?

One way would be to create a temporary mapping for every page table page the kernel wants to access, but this is inefficient. The solution is a clever trick called page table self-mapping or recursive page table mapping.

The trick is to dedicate one specific PML4 entry to point back to the physical base of the PML4 table itself. This creates a recursive mapping. For example if we choose PML4[493] as as the self-mapping entry that serve as the PTE base virtual address. Then whenever we want to read/write the PTE using its virtual address, this entry will be consulted and give the start address of the PML4 table; then MMU uses the next 9 bits to index into the PDPT table. Thus the PML4 table becomes PDPT simultaneously!

By carefully crafting a virtual address, we can make the MMU "walk" the page table hierarchy and land on any page table structure (PDPT, PDT, or PT) as if it were a final data page. This effectively maps the entire page table hierarchy for the current process into a dedicated region of the virtual address space.

## How to quickly obtain the virtual address of PTEs for any given virtual address that requires translation?

Note that we have to know the virtual address of PTEs to read/write them; and we have page table self-mapped. Is there a quick way to calculate the PTE that corresponds to a given virtual address at any given level? For example, given a virtual address `0xdeadbeef` we try to translate, how to know the virtual address of its PDPT entry?

Let's first de-construct this address to obtain the index of the entry at each level:

1. The index of the PML4  entry = (0xdeadbeef >> (12 + 3 * 9)) & 0x1ff = 0
2. The index of the PDPT  entry = (0xdeadbeef >> (12 + 2 * 9)) & 0x1ff = 3
3. The index of the PDP   entry = (0xdeadbeef >> (12 + 1 * 9)) & 0x1ff = 245
4. The index of the PTE   entry = (0xdeadbeef >> (12 + 0 * 9)) & 0x1ff = 219

Then we have (see get_pte_address):
       pte               pde               pdpe                pml4
addr:  fffff680006f56d8, fffff6fb400037a8, fffff6fb7da00018,   fffff6fb7dbed000
       [493, 0, 3, 245]  [493, 493, 0, 3]  [493, 493, 493, 0]  [493, 493, 493, 493] <- must be present (by construction of the root table)

vaddr: [0, 3, 245, 219]

493 index actually "cancels" this translation level so that by adding that to the translation path, we are "lifted" one level up.
