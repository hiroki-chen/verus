use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(T)]
pub struct UnsafeCell<T> {
    data: T,
}

impl<T> UnsafeCell<T> {
    pub const fn new(data: T) -> Self {
        UnsafeCell { data }
    }

    pub fn get(&self) -> &T {
        &self.data
    }
}

} // verus!
