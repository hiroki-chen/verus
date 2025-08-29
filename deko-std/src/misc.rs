use vstd::prelude::*;

use crate::prelude::*;

verus! {

impl<V: WellFormed> WellFormed for vstd::cell::PointsTo<V> {
    closed spec fn wf(&self) -> bool {
        true
    }
}

pub trait IsConstant {
    spec fn is_constant(&self) -> bool;
}

#[verifier::external_body]
pub proof fn lemma_is_constant_implies_constant<T: IsConstant, U: IsConstant>(
    v: T,
    f: spec_fn(T) -> U,
)
// f (c) is constant. <==> v is constant

    ensures
        v.is_constant() ==> f(v).is_constant(),
{
}

#[verifier::external_body]
pub proof fn lemma_is_constant_implies_constant_rev<T: IsConstant, U: IsConstant>(
    v: T,
    f: spec_fn(T) -> U,
)
// f (c) is constant. <==> v is constant

    ensures
        f(v).is_constant() ==> v.is_constant(),
{
}

impl<T: IsConstant> IsConstant for Option<T> {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        match self {
            Option::None => true,
            Option::Some(t) => t.is_constant(),
        }
    }
}

impl IsConstant for () {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        true
    }
}

impl<T1: IsConstant, T2: IsConstant> IsConstant for (T1, T2) {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        self.0.is_constant() && self.1.is_constant()
    }
}

impl<T> IsConstant for Ghost<T> {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        true
    }
}

impl<T> IsConstant for Tracked<T> {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        true
    }
}

} // verus!
#[macro_export]
macro_rules! impl_spec_constant_for_basic {
    ($($type: ty),* $(,)?) => {
        $(verus!{
            impl IsConstant for $type {
                #[verifier(inline)]
                open spec fn is_constant(&self) -> bool
                {
                    true
                }

            }
        }
)*
    }
}
impl_spec_constant_for_basic! {u64, u32, u16, usize, u8, bool, char, i8, i16, i32, i64}

/// A macro to lift a function to a closure that can be used in some special contexts. For
/// example, we need a closure to be used in `.map` or `filter` methods. In such cases, if
/// the closure needs to capture the environment, Verus cannot automatically "inherit" some
/// properties from it so we need to manually lift the function to a closure and add proxy
/// pre-conditions and post-conditions.
macro_rules! lift_to_closure {
    ($func:ident, $type:ty, $returning:ty, $requires:tt, $ensures: tt) => {
        paste::paste! {
            pub fn [$func _closure](__thing: $type) -> (
                res: (
                    ($returning,),
                    $type,
                )
            )
            requires
                $requires,
            ensures
                $ensures,
             {
                let mut __thing = __thing;
                let res = __thing.$func();

                (res, __thing)
            }
        }
    };
}
