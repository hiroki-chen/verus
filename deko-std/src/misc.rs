use vstd::prelude::*;

use crate::prelude::*;

verus! {

/// Trait that defines safe casting relationships between types.
/// Only types that implement this trait for each other can be safely cast.
/// This prevents arbitrary casting while allowing legitimate conversions.
///
/// Note that we do not check the semantics behind the specifications,
/// we assume if if there are legitimate convertion between two types,
/// the developers have a basic understanding of the semantics and
/// provide correct specifications.
pub trait SafeCastInto<T: WellFormed + Sized>: WellFormed + Sized {
    /// Specification function that defines when casting is valid
    spec fn cast_valid(&self) -> bool;

    spec fn cast_into(from: Self) -> T
        recommends
            Self::cast_valid(&from),
    ;
}

// identity cast.
impl<T: WellFormed + Sized> SafeCastInto<T> for T {
    open spec fn cast_valid(&self) -> bool {
        true
    }

    open spec fn cast_into(from: Self) -> T {
        from
    }
}

#[verifier::external_body]
pub fn raw_vmgexit() {
    unsafe {
        core::arch::asm!("rep; vmmcall", options(att_syntax));
    }
}

/// A tool for lifting the Seq into proof mode.
#[verifier::external_body]
pub proof fn tracked_new_seq<A>(len: nat, f: spec_fn(int) -> A) -> (r: Seq<A>)
    ensures
        r == Seq::new(len, |i: int| f(i)),
{
    unimplemented!();
}

#[verifier::external_body]
pub fn early_die()
    opens_invariants none
{
    unsafe {
        core::arch::asm!("ud2", options(att_syntax));
    }
}

#[verifier::external_body]
pub fn early_dbg()
    opens_invariants none
{
    unsafe {
        core::arch::asm!("hlt", options(att_syntax));
    }
}

impl<V: WellFormed> WellFormed for vstd::cell::PointsTo<V> {
    closed spec fn wf(&self) -> bool {
        true
    }
}

pub trait Constant {
    spec fn is_constant(&self) -> bool;
}

#[verifier::external_body]
pub proof fn lemma_is_constant_implies_constant<T: Constant, U: Constant>(v: T, f: spec_fn(T) -> U)
    ensures
        v.is_constant() ==> f(v).is_constant(),
{
}

#[verifier::external_body]
pub proof fn lemma_is_constant_implies_constant_rev<T: Constant, U: Constant>(
    v: T,
    f: spec_fn(T) -> U,
)
    ensures
        f(v).is_constant() ==> v.is_constant(),
{
}

impl<T: Constant> Constant for Option<T> {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        match self {
            Option::None => true,
            Option::Some(t) => t.is_constant(),
        }
    }
}

impl Constant for () {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        true
    }
}

impl<T1: Constant, T2: Constant> Constant for (T1, T2) {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        self.0.is_constant() && self.1.is_constant()
    }
}

impl<T> Constant for Ghost<T> {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        true
    }
}

impl<T> Constant for Tracked<T> {
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
            impl Constant for $type {
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

#[macro_export]
macro_rules! impl_wf_for_atomics {
    ($($name:ident),*) => {
        $(verus!{
            impl WellFormed for vstd::atomic::$name {
                open spec fn wf(&self) -> bool {
                    true
                }
            }
        }
)*
    };
}

#[macro_export]
#[verusfmt::skip]
macro_rules! with_permission {
    // Pattern 1: With attributes, lifetimes, and generic type parameters with trait bounds
    (
        $(#[$attr:meta])+
        $name:ident<$($lifetime:lifetime),* $(,)? $($generic:ident $(: $bound:path)?),*>, $($field:ident : $T:ty ),* $(,)?
    ) => {
        paste::paste! {
                                                                                            verus! {
                $(#[$attr])+
                pub tracked struct [<$name Permission>]<$($lifetime,)* $($generic $(: $bound)?),*> {
                    $($field: $T,)*
                }
            }
                                                                                        }
    };

    // Pattern 2: With attributes and generic type parameters with trait bounds (no lifetimes)
    (
        $(#[$attr:meta])+
        $name:ident<$($generic:ident $(: $bound:path)?),*>, $($field:ident : $T:ty ),* $(,)?
    ) => {
        paste::paste! {
                                                                                            verus! {
                $(#[$attr])+
                pub tracked struct [<$name Permission>]<$($generic $(: $bound)?),*> {
                    $($field: $T,)*
                }
            }
                                                                                        }
    };

    // Pattern 3: With attributes and simple identifier (no generics, no lifetimes)
    (
        $(#[$attr:meta])+
        $name:ident, $($field:ident : $T:ty ),* $(,)?
    ) => {
        paste::paste! {
                                                                                            verus! {
                $(#[$attr])+
                pub tracked struct [<$name Permission>] {
                    $($field: $T,)*
                }
            }
                                                                                        }
    };

    // Pattern 4: Lifetimes and generic type parameters with trait bounds (no attributes)
    (
        $name:ident<$($lifetime:lifetime),* $(,)? $($generic:ident $(: $bound:path)?),*>, $($field:ident : $T:ty ),* $(,)?
    ) => {
        paste::paste! {
                                                                                            verus! {
                pub tracked struct [<$name Permission>]<$($lifetime,)* $($generic $(: $bound)?),*> {
                    $(pub $field: $T,)*
                }

                impl<$($lifetime,)* $($generic $(: $bound)?),*> [<$name Permission>]<$($lifetime,)* $($generic),*> {
                    /// The id of this permission.
                    pub uninterp spec fn id(&self) -> int;

                    // Auto getter.
                    $(
                        pub open spec fn [< $field >](&self) -> $T {
                            self.$field
                        }
                    )*
                }
            }
                                                                                        }
    };

    // Pattern 5: Generic type parameters with trait bounds (no attributes, no lifetimes)
    (
        $name:ident<$($generic:ident $(: $bound:path)?),*>, $($field:ident : $T:ty ),* $(,)?
    ) => {
        paste::paste! {
                                                                                            verus! {
                pub tracked struct [<$name Permission>]<$($generic $(: $bound)?),*> {
                    $(pub $field: $T,)*
                }

                impl<$($generic $(: $bound)?),*> [<$name Permission>]<$($generic),*> {
                    /// The id of this permission.
                    pub uninterp spec fn id(&self) -> int;

                    // Auto getter.
                    $(
                        pub open spec fn [< $field >](&self) -> $T {
                            self.$field
                        }
                    )*
                }
            }
                                                                                        }
    };

    // Pattern 6: Simple identifier (no generics, no attributes, no lifetimes)
    (
        $name:ident, $($field:ident : $T:ty ),* $(,)?
    ) => {
        paste::paste! {
                                                                                            verus! {
                pub tracked struct [<$name Permission>] {
                    $(pub $field: $T,)*
                }

                impl [<$name Permission>] {
                    /// The id of this permission.
                    pub uninterp spec fn id(&self) -> int;

                    // Auto getter.
                    $(
                        pub open spec fn [< $field >](&self) -> $T {
                            self.$field
                        }
                    )*
                }
            }
                                                                                        }
    };
}

impl_spec_constant_for_basic! {u64, u32, u16, usize, u8, bool, char, i8, i16, i32, i64}
impl_wf_for_atomics!(PAtomicU8, PAtomicU16, PAtomicU32, PAtomicU64, PAtomicBool);

/// A macro to lift a function to a closure that can be used in some special contexts. For
/// example, we need a closure to be used in `.map` or `filter` methods. In such cases, if
/// the closure needs to capture the environment, Verus cannot automatically "inherit" some
/// properties from it so we need to manually lift the function to a closure and add proxy
/// pre-conditions and post-conditions.
#[allow(unused_macros)]
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
