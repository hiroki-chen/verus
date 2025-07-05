#![no_std]
#![feature(abi_x86_interrupt)]

#[cfg(target_arch = "x86")]
compile_error!("Cannot be compiled against non x86_64 architecture!");

extern crate alloc;

pub mod allocator;
pub mod boot;
pub mod cpu;
pub mod policy;

#[cfg(feature = "tdx")]
pub mod tdx;

use alloc::alloc::GlobalAlloc;

use vstd::prelude::*;

/// A global allocator for the monitor.
#[verifier::external]
#[global_allocator]
pub static ALLOC: crate::allocator::Allocator = crate::allocator::Allocator::new();

verus! {

pub open spec fn fibonacci_spec(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fibonacci_spec((n - 1) as nat) + fibonacci_spec((n - 2) as nat)
    }
}

pub proof fn lemma_fibonacci_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fibonacci_spec(i) <= fibonacci_spec(j),
    decreases j - i,
{
    if j < 2 || i == j || i == j - 1 {
        // auto
    } else {
        lemma_fibonacci_monotonic(i, (j - 1) as nat);
        lemma_fibonacci_monotonic(i, (j - 2) as nat);
    }
}

pub fn fibonacci_recur(n: u64) -> (result: u64)
    requires
        fibonacci_spec(n as nat) <= u64::MAX,
    ensures
        fibonacci_spec(n as nat) == result,
    decreases n,
{
    if n == 0 {
        return 0;
    } else if n == 1 {
        return 1;
    } else {
        let prev = fibonacci_recur(n - 1);
        let prev_prev = fibonacci_recur(n - 2);
        return prev + prev_prev;
    }
}

pub fn fibonacci(n: u64) -> (result: u64)
    requires
        fibonacci_spec(n as nat) <= u64::MAX,
    ensures
        fibonacci_spec(n as nat) == result,
{
    if n == 0 {
        return 0;
    }
    let mut prev: u64 = 0;
    let mut cur: u64 = 1;
    let mut i: u64 = 1;

    while i < n
        invariant
            0 < i <= n,
            fibonacci_spec(n as nat) <= u64::MAX,
            cur == fibonacci_spec(i as nat),
            prev == fibonacci_spec((i - 1) as nat),
        decreases n - i,
    {
        i = i + 1;
        proof {
            lemma_fibonacci_monotonic(i as nat, n as nat);
        }
        let new_cur = cur + prev;
        prev = cur;
        cur = new_cur;
    }
    cur
}

} // verus!
