use vstd::prelude::*;

verus! {

/// A marker trait for types that are well-formed.
///
/// Please be extra careful about name shadowing as sometimes it is tempting to
/// have a `type_invariant` also named as `wf` and will be closed for some types
/// like synchronization primitives. This will create unintended verification
/// errors as Verus will try to resolve the wrong `wf` function.
///
/// Be sure to call this function, if naming shadowing happens, by
/// `<Type as WellFormed>::wf(&self)`.
///
/// # Example
///
/// ```rust,norun
/// verus! {
///     struct MyType<V> { foo: V }
///
///     impl<V: WellFormed> WellFormed for MyType<V> {
///          open spec fn wf(&self) -> bool {
///              self.foo.wf()
///          }
///     }
/// }
/// ```
pub trait WellFormed {
    spec fn wf(&self) -> bool;
}

impl WellFormed for () {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl<T1: WellFormed, T2: WellFormed> WellFormed for (T1, T2) {
    open spec fn wf(&self) -> bool {
        self.0.wf() && self.1.wf()
    }
}

impl<T: WellFormed> WellFormed for Option<T> {
    #[verifier(inline)]
    open spec fn wf(&self) -> bool {
        match self {
            Option::None => true,
            Option::Some(t) => t.wf(),
        }
    }
}

impl<T> WellFormed for Ghost<T> {
    #[verifier(inline)]
    open spec fn wf(&self) -> bool {
        true
    }
}

impl<T> WellFormed for Tracked<T> {
    #[verifier(inline)]
    open spec fn wf(&self) -> bool {
        true
    }
}

#[macro_export]
    macro_rules! impl_spec_wf_for_basic {
        ($($type: ty),* $(,)?) => {
            $(verus!{
                impl WellFormed for $type {
                    #[verifier(inline)]
                    open spec fn wf(&self) -> bool
                    {
                        true
                    }
                }
            })*
        }
    }

impl_spec_wf_for_basic!{u64, u32, u16, usize, u8, bool, char, i8, i16, i32, i64}

} // verus!
