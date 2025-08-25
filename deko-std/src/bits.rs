use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

#[macro_export]
macro_rules! deko_bitflags {
    (
        $(#[$outer:meta])*
        $vis:vis struct $name:ident: $T:ty {
            $(
                $(#[$inner:ident $($args:tt)*])*
                const $Flag:tt = $value:literal;
            )*
        }

        $($t:tt)*
    ) => {
        verus! {
        $($vis const $Flag:$T = (1 as $T) << $value;)*

        #[allow(non_camel_case_types)]
            $vis ghost enum $name {
                $(
                    $(#[$inner $($args)*])*
                    $Flag,
                )*
            }

            impl $name {
                pub open spec fn bit(&self) -> $T {
                    match self {
                        $(
                            $name::$Flag => $value,
                        )*
                    }
                }
            }

        } // verus!

        paste::paste! {
            verus! {

            $vis struct [<$name Flags>] {
                /// Store the bitflags as a value of type T.
                bits: $T,
                /// For verification only.
                flags: vstd::prelude::Ghost<vstd::set::Set<$name>>,
            }

            pub open spec fn from_bits(bits: $T) -> Set<$name> {
                vstd::set::Set::new(|flag: $name| flag.bit() & bits != 0)
            }

            impl vstd::view::View for [<$name Flags>] {
                type V = vstd::set::Set<$name>;

                closed spec fn view(&self) -> Self::V {
                    self.flags@
                }
            }


            impl WellFormed for [<$name Flags>] {
                open spec fn wf(&self) -> bool {
                    self.inv()
                }
            }

            impl [<$name Flags>] {
                pub open spec fn inv(&self) -> bool {
                    &&& forall|flag: $name| #[trigger]
                        self@.contains(flag) <==> (flag.bit() & self.bits() != 0)
                    &&& self@ =~= from_bits(self.bits())
                }

                pub closed spec fn bits(&self) -> $T {
                    self.bits
                }

                pub fn contains(&self, flag: $T) -> (r: bool)
                    requires
                        self.wf(),
                    ensures
                        r == from_bits(flag).subset_of(self@),
                {
                    let res = flag & self.bits == flag;
                    proof {
                        let ghost other = from_bits(flag);
                        assert(other =~= vstd::set::Set::new(|s: $name| s.bit() & flag != 0));
                        assert(self@ =~= from_bits(self.bits()));

                        assert(forall|s: $name| #[trigger]
                            self@.contains(s) <==> (s.bit() & self.bits() != 0));
                        assert(forall|s: $name| #[trigger] other.contains(s) <==> s.bit() & flag != 0);

                        // ==> Direction: If the bitwise check passes, then it's a subset.
                        if res {
                            assert forall|s: $name| (#[trigger] s.bit() & flag != 0) implies (s.bit()
                                & self.bits != 0) by {
                                assert(flag & self.bits == flag);
                                assert(s.bit() & flag != 0);

                                [<lemma_ $T _subset>](flag, self.bits, s.bit());
                            }
                        }
                        if other.subset_of(self@) {
                            assert(forall|s: $name| #[trigger]
                                other.contains(s) ==> s.bit() & flag != 0 && s.bit() & self.bits != 0);
                            assume(flag & self.bits() == flag);
                        }
                    }

                    res
                }

                pub fn empty() -> (r: Self)
                    ensures
                        r.inv(),
                        r.bits() == 0,
                {
                    proof {
                        assert forall|flag: $name| (#[trigger] flag.bit() & 0) == 0 by {
                            deko_std::prelude::bit64_and_auto();
                        }
                        // Necessary
                        assert(vstd::set::Set::empty() =~= from_bits(0));
                    }

                    [<$name Flags>] { bits: 0, flags: Ghost(vstd::set::Set::empty()) }
                }
            }

            } // verus!
        }
    };
}

verus! {

#[verifier::bit_vector]
pub const proof fn bit64_and_auto()
    ensures
        forall|a: u64, b: u64| #[trigger] (a & b) == b & a,
        forall|a: u64, b: u64, c: u64| #[trigger] ((a & b) & c) == a & (b & c),
        forall|a: u64| #[trigger] (a & a) == a,
        forall|a: u64| #[trigger] (a & 0) == 0,
        forall|a: u64| #[trigger] (a & 0xffffffffffffffffu64) == a,
        forall|a: u64, b: u64| #[trigger] (a & b) <= b && (a & b) <= a,
        forall|a: u32, b: u32| #[trigger] (a & b) <= b,
        forall|a: u16, b: u16| #[trigger] (a & b) <= b,
        forall|a: u8, b: u8| #[trigger] (a & b) <= b,
{
}

#[verifier::bit_vector]
pub proof fn lemma_xor_is_or_minus_and()
    ensures
        forall|a: u64, b: u64| #[trigger] (a ^ b) == (a | b) - (a & b),
        forall|a: u32, b: u32| #[trigger] (a ^ b) == (a | b) - (a & b),
        forall|a: u16, b: u16| #[trigger] (a ^ b) == (a | b) - (a & b),
        forall|a: u8, b: u8| #[trigger] (a ^ b) == (a | b) - (a & b),
{
}

#[verifier::bit_vector]
pub proof fn lemma_u32_subset(a: u32, b: u32, c: u32)
    requires
        a & b == a,
        c & a != 0,
    ensures
        c & b != 0,
{
}


#[verifier::bit_vector]
pub proof fn lemma_u64_subset(a: u64, b: u64, c: u64)
    requires
        a & b == a,
        c & a != 0,
    ensures
        c & b != 0,
{
}


pub proof fn lemma_lt_is_power_of_two_bitor(p: u64, x: u64, y: u64, n: u64)
    requires
        0 <= n < 64,
        pow(2, n as nat) == p,
        x < p,
        y < p,
    ensures
        (x | y) < p,
{
    if p == 1 {
        // As per the documentation of Verus, "The prover does not have access
        // to any prior context except that which is given in the requires clause,
        // if provided. If the requires clause is provided, then the bit vector
        // solver attempts to prove Q ==> P. Verus will also check (using its
        // normal solver) that Q holds from the prior proof context."
        assert((x | y) == 0) by (bit_vector)
            requires
                x == 0 && y == 0,
        ;
    } else {
        lemma_u64_pow2_no_overflow(n as _);
        lemma_u64_shl_is_mul(1u64, n);
        lemma_pow2(n as nat);

        assert((x | y) < p) by (bit_vector)
            requires
                p == (1u64 << n) && x < p && y < p,

    }
}

} // verus!
