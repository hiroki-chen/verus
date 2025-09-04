use vstd::prelude::*;

use crate::prelude::*;

verus! {

#[verifier(inline)]
pub spec const VADDR_MAX_BITS: nat = 48;

#[verifier(inline)]
pub const VADDR_LOWER_MASK: u64 = 0x0000_7FFF_FFFF_FFFFu64;

#[verifier(inline)]
pub const VADDR_UPPER_MASK: u64 = 0xFFFF_8000_0000_0000u64;

#[verifier(inline)]
pub const VADDR_RANGE_SIZE: u64 = 0x1_0000_0000_0000u64;

pub const PTE_BASE: VirtAddr = VirtAddr(0xFFFFF68000000000);

#[verifier(inline)]
pub open spec fn check_sign_bit(addr: u64) -> bool {
    addr & (1u64 << 47) == 1u64 << 47
}

#[verifier(inline)]
pub open spec fn vaddr_lower_bits(addr: u64) -> u64 {
    addr & VADDR_LOWER_MASK
}

#[verifier(inline)]
pub open spec fn vaddr_upper_bits(addr: u64) -> u64 {
    addr & VADDR_UPPER_MASK
}

pub open spec fn sign_extend_impl(addr: u64) -> u64 {
    if check_sign_bit(addr) {
        (vaddr_lower_bits(addr) + VADDR_UPPER_MASK) as u64
    } else {
        vaddr_lower_bits(addr)
    }
}

pub closed spec fn sign_extend_spec(addr: u64) -> u64
    recommends
        addr < VADDR_RANGE_SIZE,
{
    if addr <= VADDR_LOWER_MASK {
        addr
    } else if addr < VADDR_RANGE_SIZE {
        (addr - VADDR_LOWER_MASK - 1 + VADDR_UPPER_MASK) as u64
    } else {
        sign_extend_impl(addr)
    }
}

pub proof fn lemma_sign_extend_make_canonical(addr: u64, ret: u64)
    requires
        sign_extend_ensures(addr, ret),
    ensures
        ret <= VADDR_LOWER_MASK || ret >= VADDR_UPPER_MASK,
{
    admit();
}

#[verifier(inline)]
pub open spec fn sign_extend_ensures(addr: u64, ret: u64) -> bool {
    &&& ret == sign_extend_spec(addr)
    &&& vaddr_lower_bits(ret) == vaddr_lower_bits(addr)
}

pub const fn sign_extend(addr: u64) -> (r: u64)
    // No requirements - accepts any u64
    ensures
        sign_extend_ensures(addr, r),
{
    let mask = 1u64 << 47;

    let v = if (addr & mask) == mask {
        addr | VADDR_UPPER_MASK
    } else {
        addr & VADDR_LOWER_MASK
    };

    proof {
        admit();
    }

    v
}

#[derive(Clone, Copy)]
pub struct MappingSpace {
    pub kernel: FixedAddressMappingRange,
    pub physmap: FixedAddressMappingRange,
}

pub struct MappingSpacePred;

impl Predicate<MappingSpace> for MappingSpacePred {
    open spec fn inv(self, v: MappingSpace) -> bool {
        v.wf()
    }
}

#[derive(Clone, Copy)]
pub struct FixedAddressMappingRange {
    virt_start: VirtAddr,
    virt_end: VirtAddr,
    phys_start: PhysAddr,
}

impl WellFormed for FixedAddressMappingRange {
    closed spec fn wf(&self) -> bool {
        Self::valid_mapping_range(self.virt_start, self.virt_end, self.phys_start)
    }
}

impl WellFormed for MappingSpace {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.kernel.wf()
        &&& self.physmap.wf()
    }
}

impl FixedAddressMappingRange {
    pub open spec fn valid_mapping_range(
        virt_start: VirtAddr,
        virt_end: VirtAddr,
        phys_start: PhysAddr,
    ) -> bool {
        true
        // &&& virt_start.wf()
        // &&& virt_end.wf()
        // &&& phys_start.wf()
        // &&& virt_start@ % 0x1000 == phys_start@ % 0x1000
        // &&& virt_end@ > virt_start@
        // &&& virt_end@ - virt_start@ + phys_start@ < u64::MAX + 1
    }

    pub fn new(virt_start: VirtAddr, virt_end: VirtAddr, phys_start: PhysAddr) -> (r: Self)
        requires
            Self::valid_mapping_range(virt_start, virt_end, phys_start),
        ensures
            r.wf(),
    {
        Self { virt_start, virt_end, phys_start }
    }

    // todo: hack this; will fix later.
    #[verifier::external_body]
    pub fn phys_to_virt(&self, paddr: PhysAddr) -> (vaddr: Option<VirtAddr>)
        requires
            self.wf(),
            paddr.wf(),
        ensures
            // vaddr.wf(),
    {
        // This is invalid.
        if paddr.0 < self.phys_start.0 {
            return None;
        }
        let size = self.virt_end.0 - self.virt_start.0;
        if paddr.0 - self.phys_start.0 >= size {
            return None;
        }
        let vaddr = self.virt_start.0 + (paddr.0 - self.phys_start.0);

        // Add the offset to the virt base.
        Some(VirtAddr::new(vaddr))
    }
}

impl MappingSpace {
    pub fn phys_to_virt(&self, paddr: PhysAddr) -> (vaddr: Option<VirtAddr>)
        requires
            self.wf(),
            paddr.wf(),
        ensures
            // vaddr.wf(),
    {
        match self.kernel.phys_to_virt(paddr) {
            Some(vaddr) => Some(vaddr),
            None => self.physmap.phys_to_virt(paddr),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct VirtAddr(pub u64);

impl View for VirtAddr {
    type V = u64;

    open spec fn view(&self) -> u64 {
        self.0
    }
}

impl VirtAddr {
    /// In x86-64, virtual addresses must be in canonical form:
    /// - bits 0-47 are the address
    /// - bits 48-63 must be copies of bit 47 (i.e., sign-extended)
    /// 
    /// This creates two valid ranges:
    /// - `0x0000_0000_0000_0000` to `0x0000_7FFF_FFFF_FFFF` (user space)
    /// - `0xFFFF_8000_0000_0000` to `0xFFFF_FFFF_FFFF_FFFF` (kernel space)
    #[inline]
    pub const fn make_canonical(addr: u64) -> (r: Self)
        ensures
            r.wf(),
    {
        let ret = sign_extend(addr);

        proof {
            lemma_sign_extend_make_canonical(addr, ret);
        }

        Self(ret)
    }

    #[inline]
    pub const fn new(addr: u64) -> (r: Self)
        ensures
            r.wf(),
    {
        Self::make_canonical(addr)
    }
}

impl WellFormed for VirtAddr {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        // Address must be canonical (48-bit with sign extension)
        self@ <= 0x0000_7FFF_FFFF_FFFF ||  // User space range
        self@ >= 0xFFFF_8000_0000_0000      // Kernel space range
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct PhysAddr(pub u64);

impl View for PhysAddr {
    type V = u64;

    open spec fn view(&self) -> u64 {
        self.0
    }
}

impl WellFormed for PhysAddr {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

impl From<u64> for VirtAddr {
    fn from(value: u64) -> (r: Self)
    {
        VirtAddr::new(value)
    }
}

impl From<u32> for VirtAddr {
    fn from(value: u32) -> (r: Self)
    {
        VirtAddr::new(value as u64)
    }
}

impl From<u64> for PhysAddr {
    fn from(value: u64) -> (r: Self)
        ensures
            r@ === value,
    {
        PhysAddr(value)
    }
}

impl From<u32> for PhysAddr {
    fn from(value: u32) -> (r: Self)
        ensures
            r@ === value as u64,
    {
        PhysAddr(value as u64)
    }
}

impl<T> From<*const T> for VirtAddr {
    fn from(value: *const T) -> Self {
        VirtAddr::new(value as u64)
    }
}

impl<T> From<*const T> for PhysAddr {
    fn from(value: *const T) -> Self {
        PhysAddr(value as u64)
    }
}

impl<T> From<*mut T> for VirtAddr {
    fn from(value: *mut T) -> Self {
        VirtAddr::new(value as u64)
    }
}

impl<T> From<*mut T> for PhysAddr {
    fn from(value: *mut T) -> Self {
        PhysAddr(value as u64)
    }
}

} // verus!
