use deko_std::cpu::CpuCore;
use vstd::prelude::*;

use super::Snp;

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
    /// PVALIDATE takes a page size as an input parameter indicating that either a
    /// 4KB or 2MB page should be validated.
    ///
    /// If the guest attempts to validate a page that is not mapped to the specified size,
    /// e.g., a 4KB page is specified but the address is mapped to a 2MB page, a `VMEXIT`
    /// will occur to indicate an NPF. The reverse will generate a `FAIL_SIZE_MISMATCH`.
    ///
    /// Returns the return value and the changed bit of CF.
    #[verifier::external_body]
    pub fn pvalidate(vaddr: u64, psize: u64, validate: bool, Tracked(perm): Tracked<()>) -> (r: (
        u64,
        bool,
    ))
        requires
            psize == 0x1000,
            vaddr % 0x1000 == 0,
    // todo: add more requirements here since we can track permission of the memory.

    {
        let rax = vaddr;
        let ret: u64;
        let rcx = 0u64;  // as we do not support huge pages we just assume 0.
        let cf: u64;
        let rdx = validate as u64;

        unsafe {
            core::arch::asm!(
                "xorq %r8, %r8",
                "pvalidate",
                "adcq %r8, %r8",
                in("rax")  rax,
             in("rcx")  rcx,
             in("rdx")  rdx,
             lateout("rax") ret,
             lateout("r8") cf,
             options(att_syntax));
        }

        (ret, cf != 0)
    }

    #[verifier::external_body]
    pub fn rmpadjust(
        vaddr: u64,
        psize: u64,
        // attr: __RmpAttribute,
        Tracked(core): Tracked<CpuCore>,
        Tracked(core2): Tracked<CpuCore>,
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
