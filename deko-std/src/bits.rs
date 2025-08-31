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

            impl deko_std::prelude::WellFormed for $name {
                open spec fn wf(&self) -> bool {
                    true
                }
            }

            impl $name {
                pub open spec fn bit(&self) -> $T {
                    match self {
                        $(
                            $name::$Flag => (1 as $T) << $value,
                        )*
                    }
                }
            }

        } // verus!
        paste::paste! {
                                                                                        verus! {
            #[allow(non_upper_case_globals)]
            $vis const [<$name _ALL_BITS>]: $T = $( (1 as $T) << $value )|*;

            #[verifier::bit_vector]
            $vis proof fn [<lemma_ $name _subset_implies_bits>](flag: $T, self_bits: $T)
                requires
                    flag & ($((1 as $T) << $value)|*) == flag,
                    $(
                        (flag & ((1 as $T) << $value) != 0) ==> (((1 as $T) << $value) & self_bits != 0)
                    ),*
                ensures
                    flag & self_bits == flag
            {}

            #[verifier::bit_vector]
            $vis proof fn [<lemma_ $name _bit_valid>](v: $T)
                requires
                    $(
                        v == (1 as $T) << $value
                    )||*
                ensures
                    v & ($((1 as $T) << $value)|*) == v
            {}

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
                    &&& self.inv()
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

                #[verifier::spinoff_prover]
                #[inline(always)]
                pub fn contains(&self, flag: $T) -> (r: bool)
                    requires
                        self.wf(),
                        flag & [<$name _ALL_BITS>] == flag,  // flag only has valid bits set
                    ensures
                        r == from_bits(flag).subset_of(self@),
                {
                    let res = flag & self.bits == flag;
                    proof {
                        let ghost other = from_bits(flag);
                        assert(other =~= vstd::set::Set::new(|s: $name| s.bit() & flag != 0));
                        assert(self@ =~= from_bits(self.bits()));
                        assert(forall |flag: $name| {
                            #[trigger]
                            $(flag.bit() == (1 as $T) << $value)||*
                        });

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

                        // The key is to decompose flag into its individual bits and
                        // use the subset relationship.
                        if other.subset_of(self@) {
                            assert(forall |status: $name|
                                #[trigger] status.bit() & self.bits != 0 <==> self@.contains(status)
                            );
                            // from subset_of.
                            assert(forall |status: $name|
                                #[trigger] other.contains(status) ==> self@.contains(status)
                            );
                            // From definition of `other`.
                            assert(other =~= vstd::set::Set::new(|status: $name| status.bit() & flag != 0));

                            $(
                                if flag & ((1 as $T) << $value) != 0 {
                                    assert(other.contains($name::$Flag)) by {
                                        // Apply commutativity of `&` to isolate the bit.
                                        deko_std::bits::bit64_and_auto();
                                        deko_std::bits::bit32_and_auto();
                                    }
                                    assert(self@.contains($name::$Flag));
                                    assert(self.bits & ((1 as $T) << $value) != 0) by {
                                        deko_std::bits::bit64_and_auto();
                                        deko_std::bits::bit32_and_auto();
                                    }
                                }
                            )*

                            // Now combine all the facts
                            let bits = self.bits;
                            assert(flag & bits == flag) by (bit_vector)
                                requires
                                    flag &
                                    ($( (1 as $T) << $value )|*) == flag,
                                    $(
                                        (flag & ((1 as $T) << $value) != 0) ==> (((1 as $T) << $value) & bits != 0)
                                    ),*
                            ;
                        }
                    }

                    res
                }

                #[inline(always)]
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

                #[inline(always)]
                #[verifier::spinoff_prover]
                pub fn all_bits() -> (r: Self)
                    ensures
                        r.inv(),
                        r.bits() == $( (1 as $T) << $value )|*,
                {
                    let ghost set = vstd::set::Set::full();
                    let all_bits: $T = [<$name _ALL_BITS>];

                    proof {
                        // proving r.inv() is non-trivial.
                        assert(
                            $(
                                ((all_bits) & ((1 as $T) << $value) != 0)
                            )&&*
                        ) by (bit_vector)
                            requires
                                all_bits == ($( ((1 as $T) << $value) )|*);

                        assert(forall |flag: $name| {
                            #[trigger]
                            $(flag.bit() == (1 as $T) << $value)||*
                        });

                        assert forall|flag: $name| (#[trigger] flag.bit() & all_bits) != 0 by {
                            deko_std::prelude::bit32_and_auto();
                            deko_std::prelude::bit64_and_auto();
                        }
                    }

                    [<$name Flags>] { bits: all_bits, flags: Ghost(set) }
                }


                #[inline(always)]
                pub fn remove(&mut self, flag: $T)
                    requires
                        old(self).wf(),
                        flag & [<$name _ALL_BITS>] == flag,
                    ensures
                        self.wf(),
                        self@ =~= old(self)@.difference(from_bits(flag)),
                {
                    // After self.bits & !flag, a bit is set iff it was set before AND *not in flag*
                    self.bits = self.bits & !flag;
                    self.flags = Ghost(old(self).flags.borrow().difference(from_bits(flag)));

                    // Now we need to prove inv() again.
                    proof {
                        assert(self@ =~= from_bits(self.bits)) by {
                            assert forall|s: $name| #[trigger]
                                self@.contains(s) <==> from_bits(self.bits).contains(s) by {
                                let sbit = s.bit();
                                let old_sbit = old(self).bits;

                                // Bit-level reasoning: this is equivalent to s.bit() & (old(self).bits & !flag) != 0
                                assert((sbit & old_sbit != 0 && sbit & flag == 0) <==> (sbit & (old_sbit
                                    & !flag) != 0)) by (bit_vector)
                                    requires
                                        $(sbit == ((1 as $T) << $value))||*
                                ;
                            }
                        }

                        // Proving `self@.contains(flag) <=> ...` is trivial as
                        // verus can automatically figure it out difference must
                        // produce a valid subset of that set; so we can always
                        // deduce from a stronger precondition.

                    }
                }
            }

            } // verus!
                                                                                    } // paste
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
pub const proof fn bit32_and_auto()
    ensures
        forall|a: u32, b: u32| #[trigger] (a & b) == b & a,
        forall|a: u32, b: u32, c: u32| #[trigger] ((a & b) & c) == a & (b & c),
        forall|a: u32| #[trigger] (a & a) == a,
        forall|a: u32| #[trigger] (a & 0) == 0,
        forall|a: u32| #[trigger] (a & 0xffffffffu32) == a,
        forall|a: u32, b: u32| #[trigger] (a & b) <= b && (a & b) <= a,
{
}

#[verifier::bit_vector]
pub const proof fn bit64_or_auto()
    ensures
        forall|a: u64, b: u64| #[trigger] (a | b) == b | a,
        forall|a: u64, b: u64, c: u64| #[trigger] ((a | b) | c) == a | (b | c),
        forall|a: u64| #[trigger] (a | a) == a,
        forall|a: u64| #[trigger] (a | 0) == a,
        forall|a: u64| #[trigger] (a | 0xffffffffffffffffu64) == 0xffffffffffffffffu64,
        forall|a: u64, b: u64| #[trigger] (a | b) >= b && (a | b) >= a,
        forall|a: u32, b: u32| #[trigger] (a | b) >= b,
        forall|a: u16, b: u16| #[trigger] (a | b) >= b,
        forall|a: u8, b: u8| #[trigger] (a | b) >= b,
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
