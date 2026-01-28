use deko_macros::DekoDebug;
use deko_std::address::{create_paddr_range, PhysAddr, VaddrRange};
use deko_std::deko_bitflags;
use deko_std::prelude::collections::hashmap::HashMap;
use deko_std::prelude::{VirtAddr, PAGE_SIZE};
use deko_std::std_extra::allocator::AllocatorWrapper;
use deko_std::std_extra::num::isize_abs;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::collections::Vec;
use crate::cpu::regs::no_smap_zone;
use crate::cpu::task::generate_id;
use crate::cpu::DekoCpuCtx;
use crate::crypto::aes::aes_gcm_256_key_gen;
use crate::guest::{DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode};
use crate::mm::frame_allocator::DekoAllocatorApi;
use crate::mm::paging::{bit_not_in_addr_region, strip_confidentiality_bits, PageTable};
use crate::mm::vm::TempMapping;
use crate::{kdebug, kinfo, vec};

deko_bitflags! {
    pub struct DekoFile: u32 {
        const READ = 0;
        const WRITE = 1;
        const APPEND = 2;
    }
}

verus! {

/// A regular file opened by a shadowed user application.
#[derive(DekoDebug)]
pub struct DekoUserFile {
    /// The path to the file.
    pub path: [u8; 256],
    /// The flags associated with the file (read, write, append).
    pub flags: DekoFileFlags,
    /// The current offset in the file; if minus, counts from the end of the file.
    pub offset: isize,
    /// The size of the file.
    pub size: usize,
}

impl WellFormed for DekoUserFile {
    open spec fn wf(&self) -> bool {
        &&& self.flags.wf()
        &&& self.flags.bits() & DekoFile_ALL_BITS == self.flags.bits()
        &&& isize_abs(self.offset as int) as usize <= self.size
    }
}

/// The resources associated with a shadowed user application running inside the guest VM.
/// These can be file descriptors, memory mappings, etc.
#[derive(DekoDebug)]
pub enum DekoUserAppResource {
    /// A regular file.
    File(DekoUserFile),
    /// A network socket.
    Socket,
}

impl WellFormed for DekoUserAppResource {
    open spec fn wf(&self) -> bool {
        match self {
            DekoUserAppResource::File(f) => f.wf(),
            DekoUserAppResource::Socket => true,
        }
    }
}

/// A shadowed user application running inside the guest VM.
pub struct DekoUserApp {
    /// The unique identifier for this user application.
    pub id: u64,
    /// Opened resources associated with this user application.
    ///
    /// These are typically file descriptors mapped to files or sockets.
    pub opened_files: HashMap<u64, DekoUserAppResource, DekoAllocatorApi>,
    /// The AES-GCM-256 key used for transparently encrypting/decrypting
    /// this user application's data if (label  ̸⊆ label_public).
    pub key: [u8; 32],
    /// Occupied memory regions by this user application.
    pub occupied_regions: Vec<VaddrRange>,
    /// Sha3-384 measurement of the user application's binary.
    pub measurement: [u8; 48],
}

impl WellFormed for DekoUserApp {
    open spec fn wf(&self) -> bool {
        &&& forall|fd: u64|
            #![trigger self.opened_files@[fd]]
            self.opened_files@.contains_key(fd) ==> self.opened_files@[fd].wf()
        &&& forall|i: int|
            #![trigger self.occupied_regions@[i]]
            0 <= i && i < self.occupied_regions.len() as int ==> {
                &&& self.occupied_regions@[i].wf()
                // must be on the user side.
                &&& self.occupied_regions@[i].end@ <= 0x8000_0000_0000
            }
    }
}

#[verus_verify]
impl DekoUserApp {
    /// Creates a new [`DekoUserApp`] with a unique id, an empty set of opened files,
    /// and a randomly generated AES-GCM-256 key.
    #[verus_spec(r =>
        ensures
            r.wf(),
    )]
    pub fn new() -> Self {
        let id = generate_id();

        Self {
            id,
            opened_files: HashMap::new_in(AllocatorWrapper(DekoAllocatorApi {  })),
            key: {
                let mut key = [0u8;32];
                aes_gcm_256_key_gen(&mut key);
                key
            },
            occupied_regions: vec![],
            measurement: [0u8;48],
        }
    }

    /// Adds this memory region to the list of occupied regions
    /// and updates the measurement of the user application.
    #[verus_spec(
        requires
            old(self).wf(),
            region.wf(),
        ensures
            // r.wf(),
    )]
    pub fn add_and_measure(&mut self, region: VaddrRange) {
    }
}

/// Copies data from a user application's memory space into the our memory space.
///
/// This function should be called if our `cr3` is not the same as the guest's `cr3`;
/// so we need to manually walk the guest page tables to read the data.
#[verus_spec(r =>
    requires
        0 < from@,
        guest_cr3.wf(),
        guest_cr3@ % PAGE_SIZE == 0,
        guest_cr3@ + PAGE_SIZE < 0x000f_ffff_ffff_f000u64,
        from@ + len <= 0x8000_0000_0000,
)]
pub(crate) fn copy_from_user(
    guest_cr3: PhysAddr,
    from: VirtAddr,
    buf: *mut u8,
    len: usize,
) -> DekoGuestServResult<usize> {
    let offset = from.0 & 0xfff;
    proof {
        let from = from.0;

        assert(offset <= PAGE_SIZE) by (bit_vector)
            requires
                offset == from & 0xfff,
        ;
        PAGE_SIZE == 0x1000;
    }

    let from = VirtAddr(from.0 & (!0xfff));

    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let private_bit = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).private_bit;
    let shared_bit = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).shared_bit;
    let guest_cr3_p = strip_confidentiality_bits(guest_cr3.0, private_bit);

    proof {
        let cr3 = guest_cr3@;
        assert(guest_cr3_p <= cr3 && guest_cr3_p % PAGE_SIZE == 0) by (bit_vector)
            requires
                guest_cr3_p == cr3 & !(private_bit as u64),
                bit_not_in_addr_region(private_bit),
                cr3 % PAGE_SIZE == 0,
        ;
    }

    let guest_cr3 = TempMapping::new(create_paddr_range(PhysAddr(guest_cr3_p), 1)).ok_or(
        DekoGuestServError::SoftError(DekoGuestServResultCode::Busy),
    )?;

    let mapping = PageTable::walk_lvl3_guest(&guest_cr3, from, private_bit, shared_bit)?;
    if mapping.temp_mappings.len() <= 2 || mapping.temp_mappings.len() > 4 {
        kinfo!(
            "copy_from_user: unexpected number of temp mappings",
            mapping.temp_mappings.len()
        );
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let final_mapping = mapping.final_mapping().unwrap();

    // SAFETY: We have established a temporary mapping to the user application's
    // memory space; so we can safely read from it.
    unsafe { copy_from_user_same_vmpl((final_mapping.inner.start.0 + offset), buf, len) }
}

/// Different from [`copy_from_user`], this function lives within the same VMPL and
/// the same `cr3` as the user application; so we can directly read from the user
/// application's memory space with SMAP disabled.
///
/// Pointers are Linux cacnonical user-space addresses.
#[verus_spec(r =>
)]
#[inline(always)]
#[verifier::external_body]
unsafe fn copy_from_user_same_vmpl(addr: u64, buf: *mut u8, len: usize) -> DekoGuestServResult<
    usize,
> {
    kdebug!("copy_from_user_same_vmpl", addr =>hex, buf as u64 =>hex, len);

    no_smap_zone(
        ||
            {
                let src_ptr = addr as *const u8;
                let dst_ptr = buf;
                core::ptr::copy_nonoverlapping(src_ptr, dst_ptr, len);
            },
    );

    Ok(len)
}

} // verus!
