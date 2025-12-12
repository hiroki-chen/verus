use deko_std::prelude::{PaddrRange, PAGE_SIZE};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::kinfo;

verus! {

/// This is a very simpel RAM FS implementation that uses no backing
/// storage and simply maps a given physical memory range as read-only
/// file system.
///
/// In our use case no actual storage is needed so we only use it as
/// a way to provide read-only access to some data blobs for loading
/// the init process.
///
/// The monitor will finally load the Linux guest image which will
/// implement the actual file system access and we provide APIs for
/// devices to access the data.
pub struct DekoRamFs {}

#[verus_verify]
impl DekoRamFs {
    /// Creates the initial RAM FS from the given physical address range.
    #[verus_spec(
        requires
            fs_range.wf(),
            fs_range.start@ % PAGE_SIZE == 0,
            fs_range.end@ % PAGE_SIZE == 0,
    )]
    pub fn create_ram_fs(fs_range: PaddrRange) {
        // If there is no FS at all just finish the
        // setup immediately and return.
        if fs_range.end.0 - fs_range.start.0 != 0 {
            kinfo!("Creating RAM FS at physical address range:", fs_range);
        }
    }
}

} // verus!
