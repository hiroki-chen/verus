use core::marker::PhantomData;

use vstd::prelude::*;

use crate::prelude::*;

// Pointer definitions and specifications
//
// DekoPtr is a smart pointer around `DekoPtrRaw<T>` that provides
// permission-based reasoning. It is used to track the ownership and
// permissions of pointers in the Deko system.
//
// DekoPtrDest is a marker type that is used to indicate the destination
// of a `DekoPtr`.
//
// SmartPtr = DekoPtr<T>
//
// RawPtr = DekoPtrRaw<T>
// Each will have their correspoinding spec types:
// DekoPtrData<T> and DekoPtrDest<T>; and DekoPtrDestRaw.
verus! {

/// A raw pointer for inter-operability with C code.
#[repr(C)]
pub struct DekoPtrRaw<T: WellFormed + IsConstant> {
    /// The actual pointer to the value
    pub ptr: u64,
    /// For verification only; erased in runtime
    pub value: Ghost<T>,
}

#[verifier::reject_recursive_types(T)]
pub struct DekoPtr<T: WellFormed + IsConstant> {
    pub raw: DekoPtrRaw<T>,
    /// Used for permission-based reasoning.
    pub perm: Tracked<DekoPtrDest<T>>,
}

#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub tracked struct DekoPtrDest<T: WellFormed + IsConstant> {
    __marker: PhantomData<T>,
    // You cannot copy it without resorting to its parent.
    __marker2: NoCopy,
}

impl<T: WellFormed + IsConstant> DekoPtrRaw<T> {
    pub fn new(ptr: u64, value: T) -> (result: Self)
        requires
            ptr > 0x0 && ptr < u64::MAX,
        ensures
            result.ptr == ptr,
            result.value == Ghost(value),
    {
        DekoPtrRaw { ptr, value: Ghost(value) }
    }
}

impl<T: WellFormed + IsConstant> IsConstant for DekoPtrRaw<T> {
    open spec fn is_constant(&self) -> bool {
        true
    }
}

impl<T: WellFormed + IsConstant> WellFormed for DekoPtrRaw<T> {
    open spec fn wf(&self) -> bool {
        &&& self.ptr > 0x0
        &&& self.ptr < u64::MAX
        &&& self.value.wf()
    }
}

impl<T: WellFormed + IsConstant> DekoPtrRaw<T> {
    pub open spec fn id(&self) -> int {
        self.ptr as int
    }
}

impl<T: WellFormed + IsConstant> Clone for DekoPtrRaw<T> {
    fn clone(&self) -> (result: Self)
        ensures
            *self == result,
    {
        DekoPtrRaw { ptr: self.ptr, value: self.value }
    }
}

impl<T: WellFormed + IsConstant> DekoPtrDest<T> {
    pub uninterp spec fn view(&self) -> DekoPtrData<T>;
}

#[verifier::external_body]
pub tracked struct DekoPtrDestRaw {
    __marker: NoCopy,
}

} // verus!
// Some specs
verus! {

pub ghost struct DekoPtrData<T: WellFormed + IsConstant> {
    /// The value of the pointer
    pub value: Option<T>,
    /// The pointer itself
    pub ptr: int,
    /// The memory attribute.
    pub attr: (),
}

} // verus!
