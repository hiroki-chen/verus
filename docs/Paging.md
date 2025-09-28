# Page Table

The memory layout is constructed by the IGVM builder, and the initial page table is just an identity mapping that maps virtual address to their physical addresses except that they are sign extended to make them cacnonical in x86_64 mode.

The page table is also self-mapped to ensure that we can modify it through a virtual address that points to its physical address. This is often done by mapping the 490th entry of the root page table (PML) to its own physical address. The virtual address of the PML is `PTE_BASE` so we can modify "itself".

You modify the page table entries through their virtual addresses but the pointer to that stores the physical address of that virtual address. Also note that when CC is enabled, each physical address must be ORed with confidentiality bits.

```
                                                                                                                                                      
                   Also Self-Mapped                                                                                                                   
                           |                                                                                                                          
                           |                                                                                                                          
                           |                                                                                                                          
                           |                                                           +--------------------------+                                   
                 +------------------+                                                  |                          |                                   
                 |                  |                                                  |                          |                                   
                 |                  |                                                  |       Kernel Region      |   ----------+                     
                 |------------------|                                                  |                          |             |                     
                 |                  |                                                  |                          |             |                     
                 |                  |                                                  +--------------------------+             |                     
                 |------------------|                                                                                           |------ Already Mapped
                 |                  |                                                  +--------------------------+             |                     
                 |                  |                                                  |                          |             |                     
                 |------------------|                                                  |                          |             |                     
                 |       PTE        |----+                                             |       Heap Region        |   ----------+                     
                 |                  |    |                                             |                          |                                   
                 +------------------+    |                                             |                          |                                   
                         PML             | VirtAddr translated by self-mapping of PML  +--------------------------+                                   
                                         |                                                          |                                                 
                                         |                                                          |                                                 
                                         |                                                          |                                                 
               +--------------------------+                                                         |                                                 
               |                          |                                                         |                                                 
               |                          |                       PhysToVirt                        |                                                 
               |      Deko Monitor        | --------------------------------------------------------+                                                 
               |                          |                                                                                                           
               |                          |                                                                                                           
               +--------------------------+                                                                                                           
```
## Abstract Model of the Page Table and Verification

An "abstract model" in Verus is a purely mathematical specification We'll use Verus's built-in spec types, primarily `Map`, to define what a page table is in terms of its behavior, completely ignoring implementation details like the 4-level structure.