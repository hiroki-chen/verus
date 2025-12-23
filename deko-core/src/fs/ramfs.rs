use deko_std::mem::bitalloc::{DekoBitAlloc, DekoBitmapAllocator1024};
use deko_std::prelude::{PaddrRange, PAGE_SIZE};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::cpu::DekoCpuCtx;
use crate::{kinfo, kpanic_if, kwarn};

verus! {

/// Initializes the RAM FS subsystem.
#[verus_spec(
    requires
        addr_range.start@ <= addr_range.end@,
        addr_range.start@ % PAGE_SIZE == 0,
        addr_range.end@ % PAGE_SIZE == 0,
)]
pub fn init_ramfs(addr_range: PaddrRange) {
    if addr_range.end.0 - addr_range.start.0 == 0 {
        kwarn!("No RamFS detected:", addr_range);
        return ;
    }
    kinfo!("Initializing RAM FS subsystem:", addr_range);

    // Create temporary mappings so that we can access the RAM FS data.
    let (this_cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let mut this_cpu_taken = this_cpu.take(Tracked(&mut cpu_perm.ptr_perm));
    let nr_pages = (addr_range.end.0 - addr_range.start.0) / PAGE_SIZE;

    kpanic_if!((nr_pages >= this_cpu_taken.temp_mapping.nr_pages as u64), // reserve oen page for safety
        "RAM FS too large:", nr_pages, "pages");

    let temp_mapping = this_cpu_taken.temp_mapping.allocate(nr_pages as usize, 0);

    this_cpu.write(Tracked(&mut cpu_perm.ptr_perm), this_cpu_taken);  // put back
}

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
