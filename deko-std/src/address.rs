use vstd::prelude::*;

use crate::prelude::*;

verus! {

pub const PTE_BASE: VirtAddr = VirtAddr(0xF68000000000);

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
        &&& virt_start.wf()
        &&& virt_end.wf()
        &&& phys_start.wf()
        &&& virt_start@ % 0x1000 == phys_start@ % 0x1000
        &&& virt_end@ > virt_start@
        &&& virt_end@ - virt_start@ + phys_start@ < u64::MAX + 1
    }

    pub fn new(virt_start: VirtAddr, virt_end: VirtAddr, phys_start: PhysAddr) -> (r: Self)
        requires
            Self::valid_mapping_range(virt_start, virt_end, phys_start),
        ensures
            r.wf(),
    {
        Self { virt_start, virt_end, phys_start }
    }

    pub fn phys_to_virt(&self, paddr: PhysAddr) -> (vaddr: Option<VirtAddr>)
        requires
            self.wf(),
            paddr.wf(),
        ensures
            vaddr matches Some(vaddr) ==> vaddr.wf(),
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
        proof {
            let vaddr = vaddr@;
            let virt_end = self.virt_end@;
            let ptr_base = PTE_BASE@;
            let val1 = (virt_end & 0x0000_FFFF_FFFF_F000u64) >> 9;
            let val2 = (vaddr & 0x0000_FFFF_FFFF_F000u64) >> 9;

            assert(vaddr <= virt_end);
            assume(val2 <= val1);
        }

        // Add the offset to the virt base.
        Some(VirtAddr(vaddr))
    }
}

impl MappingSpace {
    pub fn phys_to_virt(&self, paddr: PhysAddr) -> (vaddr: Option<VirtAddr>)
        requires
            self.wf(),
            paddr.wf(),
        ensures
            vaddr matches Some(vaddr) ==> vaddr.wf(),
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

impl WellFormed for VirtAddr {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& PTE_BASE@ + ((self@ & 0x0000_FFFF_FFFF_F000u64) >> 9) <= 0x0000_FFFF_FFFF_FFFFu64
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
        ensures
            r@ === value,
    {
        VirtAddr(value)
    }
}

impl From<u32> for VirtAddr {
    fn from(value: u32) -> (r: Self)
        ensures
            r@ === value as u64,
    {
        VirtAddr(value as u64)
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
        VirtAddr(value as u64)
    }
}

impl<T> From<*const T> for PhysAddr {
    fn from(value: *const T) -> Self {
        PhysAddr(value as u64)
    }
}

impl<T> From<*mut T> for VirtAddr {
    fn from(value: *mut T) -> Self {
        VirtAddr(value as u64)
    }
}

impl<T> From<*mut T> for PhysAddr {
    fn from(value: *mut T) -> Self {
        PhysAddr(value as u64)
    }
}

} // verus!
