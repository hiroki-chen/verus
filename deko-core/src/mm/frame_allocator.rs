//! Implements a simple page frame allocator.

use deko_std::prelude::*;
use vstd::prelude::*;

verus! {
    /// A simple page frame allocator that allocates physical pages. This just holds a
    /// buddy allocator inside where we implement this in `deko_std`.
    pub struct DekoPageFrameAllocator(DekoBuddyAllocator<DekoHeap<HEAP_SIZE>>);

    impl DekoPageFrameAllocator {
        #[verifier::type_invariant]
        pub closed spec fn inv(&self) -> bool {
            self.0.wf()
        }

        pub fn init(&self, phys_start: u64, size: u64)
            requires
                self.wf(),
                size > 0,
                valid_heap_param(phys_start, size, HEAP_SIZE as u64),
        {
            self.0.init(phys_start, size);
        }

        pub const fn new() -> (r: Self)
            ensures
                r.wf(),
        {
            let ghost f = DekoHeapPredicate;
            let heap = DekoHeap::<HEAP_SIZE>::new(Ghost(f));

            Self(DekoBuddyAllocator::new(heap, Ghost(f)))
        }
    }

    impl WellFormed for DekoPageFrameAllocator {
        closed spec fn wf(&self) -> bool {
            self.inv()
        }
    }

    impl FrameAllocator for DekoPageFrameAllocator {
        fn allocate_frame(&self) -> (r: PhysAddr) {
            proof {
                assert(vstd::layout::is_power_2(0x8)) by (compute);
            }

            let (ptr, Tracked(raw_perm), Tracked(dealloc)) = self.0.alloc(PAGE_SIZE as _, 0x8); // 8-byte aligned

            // TODO: Modify the return value to expose provenance and other permission-related stuff.
            PhysAddr(ptr.addr() as _)
        }

        fn deallocate_frame(&self, frame: PhysAddr) {
            vstd::vpanic!("todo")
        }
    }
}
