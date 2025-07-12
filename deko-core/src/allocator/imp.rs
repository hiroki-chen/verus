use alloc::alloc::{Allocator, GlobalAlloc, Layout};

use deko_std::prelude::WellFormed;
use deko_std::sync::{Arc, Mutex};
use vstd::prelude::*;

use crate::allocator::DekoAlloc;

verus! {

pub struct DekoAllocatorImpl {
    allocator: Mutex<()>,
}

impl DekoAlloc for DekoAllocatorImpl {
    
}

impl WellFormed for DekoAllocatorImpl {
    closed spec fn wf(&self) -> bool {
        self.allocator.wf()
    }
}

impl DekoAllocatorImpl {
    // todo
    pub const fn new() -> (s: Self)
        ensures
            s.wf(),
    {
        Self {
            allocator: Mutex::new(()),
        }
    }
}

} // verus!
