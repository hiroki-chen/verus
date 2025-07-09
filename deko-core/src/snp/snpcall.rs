use vstd::prelude::*;

use super::{Snp, __RmpAttribute};

verus! {

pub const RMP_4K: u64 = 0;

pub const RMP_2M: u64 = 1;

pub const RMP_READ: u8 = 1;

pub const RMP_WRITE: u8 = 2;

pub const RMP_USER_EXE: u8 = 4;

pub const RMP_KERN_EXE: u8 = 8;

pub const RMP_NO_WRITE: u8 = RMP_READ | RMP_USER_EXE | RMP_KERN_EXE;

pub const RMP_RWX: u8 = RMP_NO_WRITE | RMP_WRITE;

impl Snp {
    #[verifier::external_body]
    pub fn rmpadjust(
        vaddr: u64,
        psize: u64,
        // attr: __RmpAttribute,
        Tracked(core): Tracked<()>,
        Tracked(core2): Tracked<()>,
        Tracked(perm): Tracked<()>,
    ) -> (ret: u64)
        requires
            true,
        ensures
            true,
    {
        let ret: u64;

        unsafe {
            core::arch::asm!(
                ".byte 0xf3,0x0f,0x01,0xf1",
                in("rax") vaddr, in("rcx") psize,
                lateout("rax") ret,
                options(nostack)
            );
        }

        ret
    }
}

} // verus!
