//! The Guest-Host Communication Block (GHCB) and related functionality.
//!
//! GHCB is a protocol/data structure usde in AMD SEV-SNP to facilitate
//! communication between the guest and the hypervisor. It is used for various
//! operations, including handling certain types of exits from the guest to the
//! hypervisor.
//!
//! In this module, we define the GHCB structure and provide functions to
//! interact with it, including sending and receiving messages via the GHCB
//! protocol.
use deko_std::prelude::*;
use deko_std::sync::RwLockToks::reader;
use vstd::atomic::PAtomicU8;
use vstd::prelude::*;

use crate::cpu::irq::no_irq_zone;
use crate::cpu::msr::{read_msr, write_msr};
use crate::cpu::{CpuData, CpuDataPermission};
use crate::mm::{virt_to_phys, DEKO_FRAME_ALLOCATOR};
use crate::snp::MSR_AMD64_SEV_ES_GHCB;

deko_bitflags! {
    pub struct GHCBHvFeatures: u64 {
        const SEV_SNP                 = 0;
        const SEV_SNP_AP_CREATION     = 1;
        const SEV_SNP_RESTR_INJ       = 2;
        const SEV_SNP_RESTR_INJ_TIMER = 3;
        const APIC_ID_LIST            = 4;
        const SEV_SNP_MULTI_VMPL      = 5;
        const SEV_PAGE_STATE_CHANGE   = 6;
        const SEV_SNP_EXT_INTERRUPTS  = 9;
    }
}

verus! {

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(non_camel_case_types)]
enum GHCBExitCode {
    RDTSC = 0x6e,
    CPUID = 0x72,
    IOIO = 0x7b,
    MSR = 0x7c,
    VMMCALL = 0x81,
    RDTSCP = 0x87,
    MMIO_READ = 0x8000_0001,
    MMIO_WRITE = 0x8000_0002,
    SNP_PSC = 0x8000_0010,
    GUEST_REQUEST = 0x8000_0011,
    GUEST_EXT_REQUEST = 0x8000_0012,
    AP_CREATE = 0x80000013,
    HV_DOORBELL = 0x8000_0014,
    HV_IPI = 0x8000_0015,
    CONFIGURE_INT_INJ = 0x8000_001B,
    DISABLE_ALT_INJ = 0x8000_001C,
    SPECIFIC_EOI = 0x8000_001D,
}

/// Commands used to communicate withe GHCB MSR.
pub const SEV_INFO_REQ: u64 = 0x02;

pub const SEV_INFO_RESP: u64 = 0x01;

pub const SNP_REG_GHCB_GPA_REQ: u64 = 0x12;

pub const SNP_REG_GHCB_GPA_RESP: u64 = 0x13;

pub const SNP_STATE_CHANGE_REQ: u64 = 0x14;

pub const SNP_STATE_CHANGE_RESP: u64 = 0x15;

pub const SNP_HV_FEATURES_REQ: u64 = 0x80;

pub const SNP_HV_FEATURES_RESP: u64 = 0x81;

pub const TERM_REQ: u64 = 0x100;

pub fn msr_register_ghcb_gpa(paddr: PhysAddr)
    requires
        paddr.wf(),
{
    let mut addr = paddr.0;

    addr |= SNP_REG_GHCB_GPA_REQ;
    let response = no_irq_zone(
        ||
            {
                write_msr(MSR_AMD64_SEV_ES_GHCB, addr);
                raw_vmgexit();
                read_msr(MSR_AMD64_SEV_ES_GHCB)
            },
    );

    if response & 0xfff != SNP_REG_GHCB_GPA_RESP {
        vstd::vpanic!("Failed to register GHCB GPA via MSR");
    }
    if response & !(0xfff) != paddr.0 {
        vstd::vpanic!("Failed to register GHCB GPA via MSR");
    }
}

/// Set a page to be shared to tell the hypervisor to re-claim it.
pub fn msr_set_page_valid(paddr: PhysAddr, valid: bool)
    requires
        paddr.wf(),
{
    let mut addr = paddr.0 & 0x0000_FFFF_FFFF_F000u64;
    if valid {
        addr |= 1u64 << 52;
    } else {
        addr |= 2u64 << 52;
    }
    addr |= SNP_STATE_CHANGE_REQ;

    // Change of the state is critical so we do this in a no-irq zone.
    let response = no_irq_zone(
        ||
            {
                write_msr(MSR_AMD64_SEV_ES_GHCB, addr);
                raw_vmgexit();
                read_msr(MSR_AMD64_SEV_ES_GHCB)
            },
    );

    if response & 0xfff != SNP_STATE_CHANGE_RESP {
        vstd::vpanic!("Failed to change the page state via GHCB");
    }
    if response & !(0xfff) != 0 {
        vstd::vpanic!("Failed to change the page state via GHCB");
    }
}

#[repr(C)]
pub struct GuestHostCommucationBlock {
    _reserved: Array<u8, 0xcb>,
    pub cpl: PAtomicU8,  // tweak: this is now `repr[(C)]`
    _reserved2: Array<u8, 0x74>,
    pub xss: u64,
    _reserved3: Array<u8, 0x18>,
    pub dr7: u64,
    _reserved4: Array<u8, 0x90>,
    pub rax: u64,
    _reserved5: Array<u8, 0x100>,
    _reserved6: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rbx: u64,
    _reserved7: Array<u8, 0x70>,
    /// Guest controlled exit code.
    pub sw_exitcode: u64,
    /// Guest controlled exit info 1.
    pub sw_exitinfo1: u64,
    /// Guest controlled exit info 2.
    pub sw_exitinfo2: u64,
    /// Guest controlled additional information.
    pub sw_scratch: u64,
    _reserved8: Array<u8, 0x38>,
    pub xcr0: u64,
    /// Bitmap to indicate valid qwords in the save state area
    /// starting from offset 0x000 through offset 0xe3f.
    pub valid_bitmap: Array<u64, 0x2>,
    pub x87_state_gpa: u64,
    _reserved9: Array<u8, 0x3f8>,
    pub shared_buffer: Array<u8, 0x7f0>,
    _reserved10: Array<u8, 0x0a>,
    /// Version of the GHCB protocol used by the guest.
    pub ghcb_protocol_version: u16,
    /// Provides an indicator of the usage and format of the GHCB:
    /// - 0x0000_0000: The GHCB page follows the format defined in
    ///                the AMD's manual.
    /// - Any other value can be used by the hypervisor, which can
    ///             determine its own format.
    pub ghcb_usage: u32,
}

impl WellFormed for GuestHostCommucationBlock {
    closed spec fn wf(&self) -> bool {
        &&& self.ghcb_protocol_version == 0x0001 || self.ghcb_protocol_version == 0x0002
        &&& self.ghcb_usage == 0x0000_0000
        &&& self.valid_bitmap.wf()
    }
}

impl GuestHostCommucationBlock {
    #[verifier::external_body]
    #[inline]
    pub fn set_rax(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoPointsTo<Self>>,
        value: u64,
    ) -> (r: Tracked<DekoPointsTo<Self>>)
        requires
            perm.wf(),
            perm.is_init(),
            perm.wf_with_val(),
            perm.pptr() == ptr@,
        ensures
            r@.wf(),
            r@.wf_with_val(),
            r@.is_init(),
            r@.pptr() == ptr@,
    {
        ptr.update_in_place(
            Tracked(perm),
            |v|
                {
                    unsafe {
                        (*v).rax = value;
                    }
                },
        )
    }

    #[verifier::external_body]
    #[inline]
    pub fn set_vmexit_info(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoPointsTo<Self>>,
        reason: u64,
        info_1: u64,
        info_2: u64,
    ) -> (r: Tracked<DekoPointsTo<Self>>)
        requires
            perm.wf(),
            perm.is_init(),
            perm.wf_with_val(),
            perm.pptr() == ptr@,
        ensures
            r@.wf(),
            r@.wf_with_val(),
            r@.is_init(),
            r@.pptr() == ptr@,
    {
        ptr.update_in_place(
            Tracked(perm),
            |v|
                {
                    let v = unsafe { &mut *v };
                    v.sw_exitcode = reason;
                    v.sw_exitinfo1 = info_1;
                    v.sw_exitinfo2 = info_2;
                    v.ghcb_usage = 0;
                    v.ghcb_protocol_version = 0x0002;
                },
        )
    }

    #[verifier::external_body]
    #[inline]
    pub fn set_valid_info(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoPointsTo<Self>>,
        index: usize,
        mask: u64,
    ) -> (r: Tracked<DekoPointsTo<Self>>)
        requires
            perm.wf(),
            perm.wf_with_val(),
            perm.is_init(),
            perm.pptr() == ptr@,
            index < perm.value().valid_bitmap()@.len(),
        ensures
            r@.wf(),
            r@.wf_with_val(),
            r@.is_init(),
            r@.pptr() == ptr@,
    {
        ptr.update_in_place(
            Tracked(perm),
            |v|
                {
                    unsafe {
                        (*v).valid_bitmap.update_in_place(index, |b: u64| { ((), b | mask) });
                    }
                },
        )
    }

    pub fn ioin(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoPointsTo<Self>>,
        port: u16,
        size: u8,
    ) -> (r: (u8, Tracked<DekoPointsTo<Self>>))
        requires
            perm.wf(),
            perm.is_init(),
            perm.wf_with_val(),
            perm.pptr() == ptr@,
            size == 1 || size == 2 || size == 4,
        ensures
            r.1@.wf(),
            r.1@.wf_with_val(),
            r.1@.is_init(),
            r.1@.pptr() == ptr@,
    {
        vstd::vpanic!("Not implemented");
    }

    /// Send bytes out to the serial port.
    pub fn ioout(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoPointsTo<Self>>,
        port: u16,
        value: u64,
        size: u8,
    ) -> (r: Tracked<DekoPointsTo<Self>>)
        requires
            perm.wf(),
            perm.is_init(),
            perm.wf_with_val(),
            perm.pptr() == ptr@,
            size == 1 || size == 2 || size == 4,
        ensures
            r@.wf(),
            r@.wf_with_val(),
            r@.is_init(),
            r@.pptr() == ptr@,
    {
        let Tracked(perm) = Self::clear(ptr, Tracked(perm));

        let mut out = (port as u64) << 16;
        match size {
            1 => out = out | 1 << 4,
            2 => out = out | 1 << 5,
            4 => out = out | 1 << 6,
            _ => {
                proof {
                    assert(false);
                }

                vstd::vpanic!("1145141919810");
            },
        }

        let Tracked(perm) = Self::set_rax(ptr, Tracked(perm), value);

        proof {
            assert((0x1F8usize >> 3) & 0x3f < 64) by (bit_vector);
            assert((0x1F8usize >> 9) & 0x1 < 2) by (bit_vector);
        }

        let Tracked(perm) = Self::set_valid(ptr, Tracked(perm), 0x1F8);  // rax.
        Self::vmexit(ptr, Tracked(perm), GHCBExitCode::IOIO as u64, out, 0)
    }

    pub closed spec fn valid_bitmap(&self) -> Array<u64, 0x2> {
        self.valid_bitmap
    }

    /// Performs a VMGEXIT.
    pub fn vmexit(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoPointsTo<Self>>,
        reason: u64,
        info_1: u64,
        info_2: u64,
    ) -> (r: Tracked<DekoPointsTo<Self>>)
        requires
            perm.wf(),
            perm.is_init(),
            perm.wf_with_val(),
            perm.pptr() == ptr@,
        ensures
            r@.wf(),
            r@.wf_with_val(),
            r@.is_init(),
            r@.pptr() == ptr@,
    {
        let Tracked(perm) = Self::set_vmexit_info(ptr, Tracked(perm), reason, info_1, info_2);

        // TODO: MAKE IT macro.
        proof {
            assert((0x3F0usize >> 3) & 0x3f < 64) by (bit_vector);
            assert((0x3F0usize >> 9) & 0x1 < 2) by (bit_vector);
            assert((0x3F8usize >> 3) & 0x3f < 64) by (bit_vector);
            assert((0x3F8usize >> 9) & 0x1 < 2) by (bit_vector);
            assert((0x390usize >> 3) & 0x3f < 64) by (bit_vector);
            assert((0x390usize >> 9) & 0x1 < 2) by (bit_vector);
            assert((0x398usize >> 3) & 0x3f < 64) by (bit_vector);
            assert((0x398usize >> 9) & 0x1 < 2) by (bit_vector);
            assert((0x3A0usize >> 3) & 0x3f < 64) by (bit_vector);
            assert((0x3A0usize >> 9) & 0x1 < 2) by (bit_vector);
            assert((0xFFCusize >> 3) & 0x3f < 64) by (bit_vector);
            assert((0xFFCusize >> 9) & 0x1 < 2) by (bit_vector);
            assert((0xFFAusize >> 3) & 0x3f < 64) by (bit_vector);
            assert((0xFFAusize >> 9) & 0x1 < 2) by (bit_vector);
        }

        let addr = virt_to_phys(VirtAddr::new(ptr.addr() as u64));
        no_irq_zone(
            ||
                {
                    write_msr(MSR_AMD64_SEV_ES_GHCB, addr.0);
                },
        );
        raw_vmgexit();

        let Tracked(perm) = Self::set_valid(ptr, Tracked(perm), 0x390);  // sw_exitcode
        let Tracked(perm) = Self::set_valid(ptr, Tracked(perm), 0x398);  // sw_exitinfo1
        let Tracked(perm) = Self::set_valid(ptr, Tracked(perm), 0x3A0);  // sw_exitinfo2
        let Tracked(perm) = Self::set_valid(ptr, Tracked(perm), 0xFFC);  // ghcb_usage
        Self::set_valid(ptr, Tracked(perm), 0xFFA)
    }

    pub fn clear(ptr: DekoPPtr<Self>, Tracked(perm): Tracked<DekoPointsTo<Self>>) -> (r: Tracked<
        DekoPointsTo<Self>,
    >)
        requires
            perm.wf(),
            perm.wf_with_val(),
            perm.is_init(),
            perm.pptr() == ptr@,
        ensures
            r@.wf(),
            r@.wf_with_val(),
            r@.is_init(),
            r@.pptr() == ptr@,
    {
        let off = 0x3F0;

        proof {
            assert((0x3F0usize >> 3) & 0x3f < 64) by (bit_vector);
            assert((0x3F0usize >> 9) & 0x1 < 2) by (bit_vector);
            assert((0x3F8usize >> 3) & 0x3f < 64) by (bit_vector);
            assert((0x3F8usize >> 9) & 0x1 < 2) by (bit_vector);
        }

        let Tracked(perm) = Self::set_valid(ptr, Tracked(perm), off);
        Self::set_valid(ptr, Tracked(perm), off + 8)
    }

    /// Set something as valid in the bitmap.
    pub fn set_valid(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoPointsTo<Self>>,
        offset: usize,
    ) -> (r: Tracked<DekoPointsTo<Self>>)
        requires
            perm.wf(),
            perm.wf_with_val(),
            perm.is_init(),
            perm.pptr() == ptr@,
            (offset >> 3) & 0x3f < 64,
            (offset >> 9 & 0x1) < perm.value().valid_bitmap()@.len(),
        ensures
            r@.wf(),
            r@.wf_with_val(),
            r@.is_init(),
            r@.pptr() == ptr@,
    // add more.

    {
        let bit: usize = (offset >> 3) & 0x3f;
        let index: usize = (offset >> 9) & 0x1;
        let mask: u64 = 1 << bit;

        Self::set_valid_info(ptr, Tracked(perm), index, mask)
    }

    /// Call this function to make GHCB structure valid.
    ///
    /// The caller should be aware that allocating GHCB on their own is
    /// strongly discouraged as the page allocated for GHCB must be
    /// properly validated using `pvalidate` and set the permission of
    /// the underlying PTE to be shared with the hypervisor. This process
    /// will need to go through MSR communication and page table walk.
    ///
    /// We do not guarantee what is on that newly allocated page, i.e.,
    /// we leave the page potentially _uninitialized_.
    pub fn validate_ghcb(cpu: DekoPPtr<CpuData>, Tracked(cpu_perm): Tracked<CpuDataPermission>)
        requires
            cpu_perm.wf_with(cpu),
    {
        let ghcb = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).ghcb();
        let vaddr = VirtAddr::new(ghcb.addr() as u64);
        let paddr = virt_to_phys(vaddr);

        proof {
            // prove it.
            assume(vaddr@ % 0x1000 == 0);
        }

        // Now to need to call `pvalidate` to invalidate this.
        crate::snp::Snp::pvalidate(vaddr.0, 0x1000, false, Tracked(()));

        msr_set_page_valid(paddr, false);

        // Map the page as shared
        CpuData::map_shared_page(cpu, vaddr, Tracked(cpu_perm));
    }
}

/// Fetch the current GHCB structure for this specific CPU core.
pub fn current_ghcb() -> (r: (
    DekoPPtr<GuestHostCommucationBlock>,
    Tracked<DekoPointsTo<GuestHostCommucationBlock>>,
))
    ensures
        r.1@.wf(),
        r.1@.is_init(),
        r.1@.wf_with_val(),
        r.1@.pptr() == r.0@,
{
    let (cpu, Tracked(perm)) = CpuData::this_cpu();
    let cpu = cpu.borrow(Tracked(&perm.ptr_perm));

    // `this_cpu` is causing page fault so the mapping is problematic.
    (cpu.ghcb(), Tracked(perm.ghcb_perm))
}

} // verus!
