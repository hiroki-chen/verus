use vstd::arithmetic::logarithm::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::math::*;
use vstd::prelude::*;

verus! {

#[verifier::inline]
pub open spec fn is_power_of_two_spec(n: nat) -> bool {
    exists|exp: nat| n == #[trigger] pow(2, exp)
}

#[verifier::inline]
pub open spec fn is_power_of_two(n: u64) -> bool {
    n > 0 && (n & (n - 1) as u64) == 0
}

pub open spec fn next_power_of_two_spec(n: nat) -> nat {
    if n == 0 || n == 1 {
        1
    } else {
        let exp = log(2, n as int) as nat;
        if pow(2, exp) == n {
            pow(2, exp) as nat
        } else {
            pow(2, exp + 1) as nat
        }
    }
}

#[verifier::inline]
/// Returns the next power of two greater than or equal to `n`.
pub open spec fn next_power_of_two_correct(n: nat, res: nat) -> bool {
    exists|e: nat|
        if n == #[trigger] pow(2, e) {
            res == n
        } else {
            res == pow(2, e + 1) && pow(2, e) < n < res
        }
}

pub assume_specification[ u64::ilog2 ](n: u64) -> (result: u32)
    requires
        n > 0,
    ensures
        result == log(2, n as int),
;

pub assume_specification[ u64::next_power_of_two ](n: u64) -> (result: u64)
    ensures
        result == next_power_of_two_spec(n as nat),
        next_power_of_two_correct(n as nat, result as nat),
;

pub assume_specification[ u64::pow ](n: u64, exp: u32) -> (result: u64)
    ensures
        result == vstd::arithmetic::power::pow(n as int, exp as nat),
;

} // verus!
