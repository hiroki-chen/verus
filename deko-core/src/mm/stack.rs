use deko_macros::DekoDebug;
use deko_std::address::{PhysAddr, VirtAddr};
use deko_std::fmt::DekoDebug;
use deko_std::mem::PAGE_SIZE;
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use super::frame_allocator::DekoAllocatorApi;
use crate::collections::Vec;
use crate::{kunimplemented, vec};

verus! {

#[derive(DekoDebug)]
pub struct DekoIstStack {
    /// Double fault stack.
    pub df_stack: Option<DekoPPtr<DekoKernelStack>>,
    /// DF shadow stack.
    pub df_ss: Option<DekoPPtr<DekoKernelStack>>,
}

/// A mapping that is used as the kernel stack.
pub struct DekoKernelStack {
    /// The allocated stack frames.
    pub alloc: Vec<Option<(VirtAddr, PhysAddr)>>,
    /// Guard pages to be allocated to the stack.
    pub guard_pages: u64,
    /// Whether this is a shadow stack.
    pub shadow: bool,
}

impl DekoDebug for DekoKernelStack {
    #[verifier::external_body]
    fn deko_debug<W: deko_std::prelude::DekoWriter>(&self, writer: &W) {
        writer.write_str("DekoKernelStack{ \n");
        writer.write_str("  alloc: ");

        for (i, entry) in self.alloc.iter().enumerate() {
            i.deko_debug(writer);
            writer.write_str(": ");
            entry.deko_debug(writer);
            writer.write_str(", ");
        }

        writer.write_str("\n}");
    }
}

impl WellFormed for DekoIstStack {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl WellFormed for DekoKernelStack {
    open spec fn wf(&self) -> bool {
        &&& forall|i: int|
            0 <= i && i < self.alloc@.len() ==> match #[trigger] self.alloc@[i] {
                Some((vaddr, paddr)) => {
                    &&& vaddr.wf() && vaddr@ % PAGE_SIZE == 0
                    &&& paddr.wf() && paddr@ % PAGE_SIZE == 0
                },
                None => true,
            }
        &&& self.guard_pages <= u8::MAX as u64  // 255 as maximum guard pages
        &&& self.alloc@.len() <= u8::MAX as int  // 255 as maximum stack size

    }
}

#[verus_verify]
impl DekoKernelStack {
    #[verifier::inline]
    pub open spec fn stack_top_spec(&self) -> u64 {
        let guard_size = self.guard_pages * PAGE_SIZE;
        let top = guard_size + self.alloc@.len() as u64 * PAGE_SIZE;

        top as u64
    }

    // Filled later.
    pub open spec fn new_with_size_spec(size: u64, shadow: bool, r: Self) -> bool {
        &&& r.wf()
        &&& r.alloc@.len() as u64 == size >> 12
        &&& forall|i: int|
            0 <= i && i < r.alloc@.len() ==> #[trigger] r.alloc@[i] == None::<(VirtAddr, PhysAddr)>
    }

    /// Get the offset of the top of the stack to the base.
    #[verifier::when_used_as_spec(stack_top_spec)]
    #[verus_spec(r =>
        requires
            self.wf(),
        ensures
            r % PAGE_SIZE == 0,
            r == self.stack_top_spec(),
    )]
    pub fn stack_top(&self) -> u64 {
        let guard_size = self.guard_pages * PAGE_SIZE;
        let top = guard_size + self.alloc.len() as u64 * PAGE_SIZE;

        top
    }

    #[verus_spec(r =>
        requires
            size % PAGE_SIZE == 0,
            size + 2 * PAGE_SIZE <= u16::MAX as u64, // to ensure no overflow the stack (65535 Bytes).
        ensures
            Self::new_with_size_spec(size, shadow, r),
    )]
    pub fn new_with_size(size: u64, shadow: bool) -> Self {
        let total_size = (size + 2 * PAGE_SIZE).next_power_of_two();
        let guard_pages = ((total_size - size) >> 12) / 2;
        let alloc_size = size >> 12;
        let mut v = Vec::with_capacity_in(alloc_size as usize, DekoAllocatorApi {  });

        let mut i = 0;
        #[verus_spec(
            invariant
                i <= alloc_size,
                v@.len() == i as int,
                forall|j: int| 0 <= j < i as int ==> #[trigger] v@[j] == None::<(VirtAddr, PhysAddr)>,
            decreases
                alloc_size - i,
        )]
        while i < alloc_size {
            v.push(None::<(VirtAddr, PhysAddr)>);
            i += 1;
        }

        proof {
            // Do this later.
            assume(guard_pages <= u8::MAX as u64);
            assume(alloc_size <= u8::MAX as u64);
        }

        Self { alloc: v, guard_pages, shadow }
    }
}

} // verus!
