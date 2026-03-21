use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExCell<T>(core::cell::Cell<T>) where T: core::marker::MetaSized + ?Sized;

pub assume_specification<T>[ core::cell::Cell::<T>::new ](_0: T) -> (r: core::cell::Cell<T>)
;

pub assume_specification<T>[ core::cell::Cell::<T>::set ](_0: &core::cell::Cell<T>, _1: T) where
    T: core::marker::Destruct,

;

pub assume_specification<T>[ core::cell::Cell::<T>::get ](_0: &core::cell::Cell<T>) -> (r: T) where
    T: core::marker::Copy,

;

} // verus!
