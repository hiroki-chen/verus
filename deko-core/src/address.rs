use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Clone, Copy, Debug, Default)]
pub struct VirtAddr(pub u64);

impl From<u64> for VirtAddr {
    fn from(value: u64) -> Self {
        VirtAddr(value)
    }
}

impl<T> From<*const T> for VirtAddr {
    fn from(value: *const T) -> Self {
        VirtAddr(value as u64)
    }
}

impl<T> From<*mut T> for VirtAddr {
    fn from(value: *mut T) -> Self {
        VirtAddr(value as u64)
    }
}

} // verus!
