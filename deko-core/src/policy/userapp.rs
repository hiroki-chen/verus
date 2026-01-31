use deko_macros::DekoDebug;
use deko_std::address::{create_paddr_range, PhysAddr, VaddrRange};
use deko_std::prelude::collections::hashmap::HashMap;
use deko_std::prelude::{VirtAddr, PAGE_SIZE};
use deko_std::std_extra::allocator::AllocatorWrapper;
use deko_std::std_extra::num::isize_abs;
use deko_std::sync::{DekoAtomicData, DekoSimpleOnceCell, DekoSimpleRwLock};
use deko_std::wf::WellFormed;
use deko_std::{deko_bitflags, TrivialPredicate};
use vstd::prelude::*;

use crate::collections::Vec;
use crate::cpu::irq::IrqSafeLockGuard;
use crate::cpu::regs::no_smap_zone;
use crate::cpu::task::{generate_id, DekoRunnableState};
use crate::cpu::DekoCpuCtx;
use crate::crypto::aes::aes_gcm_256_key_gen;
use crate::guest::service::DekoNewAppReq;
use crate::guest::{DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode};
use crate::mm::frame_allocator::DekoAllocatorApi;
use crate::mm::paging::{bit_not_in_addr_region, strip_confidentiality_bits, PageTable};
use crate::mm::vm::TempMapping;
use crate::{kdebug, kerror, kinfo, vec};

deko_bitflags! {
    pub struct DekoFile: u32 {
        const READ = 0;
        const WRITE = 1;
        const APPEND = 2;
    }
}

verus! {

pub exec static HOST_MNT_NS_ID: DekoSimpleOnceCell<u64>
    ensures
        HOST_MNT_NS_ID.wf(),
{
    DekoSimpleOnceCell::new(Ghost(()))
}

/// Tracks all currently running container runtimes inside the guest VM.
/// The identifiers are the physical addresses of their main thread's CR3.
pub exec static RUNNING_CONTAINER_RUNTIME: DekoSimpleRwLock<
    Option<HashMap<PhysAddr, (), DekoAllocatorApi>>,
    IrqSafeLockGuard,
>
    ensures
        RUNNING_CONTAINER_RUNTIME.wf(),
{
    let r = DekoSimpleRwLock::new(
        DekoAtomicData::new(None),
        IrqSafeLockGuard {  },
        Ghost(TrivialPredicate::new()),
    );

    proof {
        use_type_invariant(&r);
    }

    r
}

pub exec static IS_DOCKER_RUNNING: DekoSimpleOnceCell<()>
    ensures
        IS_DOCKER_RUNNING.wf(),
{
    DekoSimpleOnceCell::new(Ghost(()))
}

pub const RUNC_NAME: &'static str = "runc";

pub const CONTAINERD_NAME: &'static str = "containerd";

pub const CONTAINERD_SHIM_NAME: &'static str = "containerd-shim";

pub const DOCKER_OVERLAY: &'static str = "overlay";

/// Checks whether the given file path is associated with Docker or container runtimes.
#[inline]
pub fn is_docker_request(path: &str) -> bool {
    path.contains(RUNC_NAME) || path.contains(CONTAINERD_NAME) || path.contains(
        CONTAINERD_SHIM_NAME,
    )
}

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

/// A shadowed user application (mimicking task_struct) running inside the guest VM.
///
/// This structure bridges the gap between hardware reality (CR3) and
/// Linux logical abstraction (PID, Comm, Namespaces).
#[derive(DekoDebug)]
pub struct DekoUserApp {
    /// The Page Table Base Address (CR3).
    /// In a non-KPTI environment, this is the ultimate, spoof-proof identifier
    /// for the memory context of this application.
    /// Maps to: CPU register CR3 / task_struct->mm->pgd
    pub cr3: PhysAddr,
    /// The Process ID seen by the Guest Kernel.
    /// Essential for correlating with sys_wait4, logs, and user tools.
    /// Maps to: task_struct->pid
    pub pid: u32,
    /// The Thread Group ID.
    /// Essential for handling `sys_exit_group` (kill all threads).
    /// If tgid == pid, this is the main thread.
    /// Maps to: task_struct->tgid
    pub tgid: u32,
    /// The Parent's PID.
    /// Used to reconstruct the process tree.
    /// E.g., Identify if this process was spawned by `runc` or `containerd`.
    /// Maps to: task_struct->real_parent->pid
    pub parent_pid: u32,
    /// Container ID / Namespace Hash.
    /// If you track namespaces, this identifies the "Sandbox".
    /// 0 usually means Host Namespace.
    /// Maps to: Hash of (task_struct->nsproxy->mnt_ns)
    pub container_id: u64,
    /// User ID (Effective UID).
    /// Used for basic privilege checks (is this root?).
    /// Maps to: task_struct->cred->euid
    pub uid: u32,
    /// The unique identifier for this user application.
    pub id: u64,
    // Deko Security Extensions ( Your Custom Fields )
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
    // /// Creates a new [`DekoUserApp`] with a unique id, an empty set of opened files,
    // /// and a randomly generated AES-GCM-256 key.
    // #[verus_spec(r =>
    //     ensures
    //         r.wf(),
    // )]
    // pub fn new() -> Self {
    //     let id = generate_id();
    //     Self {
    //         id,
    //         opened_files: HashMap::new_in(AllocatorWrapper(DekoAllocatorApi {  })),
    //         key: {
    //             let mut key = [0u8;32];
    //             aes_gcm_256_key_gen(&mut key);
    //             key
    //         },
    //         occupied_regions: vec![],
    //         measurement: [0u8;48],
    //     }
    // }
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
    let offset_4k = from.0 & 0xfff;
    let offset_2m = from.0 & 0x1fffff;
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
    let offset = if mapping.lvl == 0 {
        offset_4k
    } else {
        offset_2m
    };

    let addr = final_mapping.inner.start.0.wrapping_add(offset);

    // Pre-filter the length to avoid overflow.
    //
    // The guest will always prepare the argument in a way such that it will
    // never cross the mapping boundary (i.e., page boundary).
    let len = len.min(final_mapping.inner.end.0.wrapping_sub(addr) as usize);

    // SAFETY: We have established a temporary mapping to the user application's
    // memory space; so we can safely read from it.
    unsafe { copy_from_user_same_vmpl((final_mapping.inner.start.0.wrapping_add(offset)), buf, len)
    }
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

/// Registers a new shadowed user application inside the guest VM.
///
/// The user applications can be either the container runtimes (e.g., runc, containerd)
/// or the actual containerized applications (e.g., nginx, redis). They are differentiated
/// via their namespace ids.
#[verus_spec(r =>
    requires
)]
pub fn register_user_app(req: &DekoNewAppReq) -> DekoGuestServResult<()> {
    let comm = core::ffi::CStr::from_bytes_until_nul(&req.comm).map_err(
        |_e| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam),
    )?.to_str().map_err(|_e| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))?;

    // When pid == 1 then the `systemd` process is being created.
    if req.pid == 1 {
        if <str as PartialEq<str>>::ne(comm, "init") && <str as PartialEq<str>>::ne(
            comm,
            "systemd",
        ) {
            kerror!(
                "[Init] Unexpected PID 1 process name:",
                &req.comm,
            );
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        kinfo!("[Init] Detected /sbin/init (PID 1). Setting Host Namespace Baseline:", req.mnt_ns_id=>hex);

        HOST_MNT_NS_ID.init(req.mnt_ns_id);
    } else {
        let host_ns = HOST_MNT_NS_ID.get().ok_or(DekoGuestServError::FatalError)?;

        if req.mnt_ns_id == *host_ns {
            // We are still in the host side; just check if this is a container runtime.
            if is_docker_request(comm) {
                kinfo!("[Registry] Detected Container Runtime:", comm, "PID:", req.pid);
            }
        }
        // TODO: Create new application and stores it in the global registry.

    }

    Ok(())
}

} // verus!
