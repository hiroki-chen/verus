use deko_std::prelude::*;
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct VirtAddr(pub u64);

impl View for VirtAddr {
    type V = u64;

    open spec fn view(&self) -> u64 {
        self.0
    }
}

impl WellFormed for VirtAddr {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        self.0 < 0x0000_8000_0000_0000
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct PhysAddr(pub u64);

impl View for PhysAddr {
    type V = u64;

    open spec fn view(&self) -> u64 {
        self.0
    }
}

impl WellFormed for PhysAddr {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        self.0 < 0x0000_8000_0000_0000
    }
}

impl From<u64> for VirtAddr {
    fn from(value: u64) -> Self {
        VirtAddr(value)
    }
}

impl From<u64> for PhysAddr {
    fn from(value: u64) -> Self {
        PhysAddr(value)
    }
}

impl<T> From<*const T> for VirtAddr {
    fn from(value: *const T) -> Self {
        VirtAddr(value as u64)
    }
}

impl<T> From<*const T> for PhysAddr {
    fn from(value: *const T) -> Self {
        PhysAddr(value as u64)
    }
}

impl<T> From<*mut T> for VirtAddr {
    fn from(value: *mut T) -> Self {
        VirtAddr(value as u64)
    }
}

impl<T> From<*mut T> for PhysAddr {
    fn from(value: *mut T) -> Self {
        PhysAddr(value as u64)
    }
}

} // verus!
