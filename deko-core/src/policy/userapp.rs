use deko_macros::DekoDebug;
use deko_std::deko_bitflags;
use deko_std::prelude::collections::hashmap::HashMap;
use deko_std::std_extra::num::isize_abs;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::collections::Vec;
use crate::cpu::regs::no_smap_zone;
use crate::guest::DekoGuestServResult;
use crate::mm::frame_allocator::DekoAllocatorApi;
use crate::vec;

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
    pub opened_files: HashMap<u64, DekoUserAppResource, DekoAllocatorApi>,
}

impl WellFormed for DekoUserApp {
    open spec fn wf(&self) -> bool {
        true
    }
}

/// Copies data from a user application's memory space into the our memory space.
#[verus_spec(r =>
    requires
        0 < from,
        from + len <= 0x8000_0000_0000,
)]
pub(crate) fn copy_from_guest_user(from: u64, len: usize) -> DekoGuestServResult<Vec<u8>> {
    // // May not mapped.
    // // `from` is a pointer in the guest VM's memory space
    // // so we need to use special mechanisms to read from it.
    // no_smap_zone(
    //     ||
    //         {
    //             let mut buffer = vec![];
    //             for i in 0..len
    //                 invariant
    //                     buffer.len() == i,
    //                     0 <= i <= len,
    //                     from + len <= 0x8000_0000_0000,
    //             {
    //                 let byte: u8;
    //                 match unsafe { try_read_user_byte(from + buffer.len() as u64) } {
    //                     Ok(b) => byte = b,
    //                     Err(e) => {
    //                         return Err(e);
    //                     },
    //                 }
    //                 buffer.push(byte);
    //             }
    //             Ok(buffer)
    //         },
    // )
    Ok(vec![])
}

#[inline(always)]
#[verifier::external_body]
unsafe fn try_read_user_byte(addr: u64) -> DekoGuestServResult<u8> {
    let ptr = addr as *const u8;

    Ok(core::ptr::read_volatile(ptr))
}

} // verus!
