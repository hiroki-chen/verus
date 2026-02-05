use deko_macros::DekoDebug;
use deko_std::address::{create_paddr_range, PhysAddr, VaddrRange};
use deko_std::prelude::collections::hashmap::HashMap;
use deko_std::prelude::{VirtAddr, PAGE_SIZE, VADDR_LOWER_MASK};
use deko_std::std_extra::allocator::AllocatorWrapper;
use deko_std::std_extra::num::isize_abs;
use deko_std::sync::{
    DekoAtomicData, DekoRwLock, DekoSimpleOnceCell, DekoSimpleRwLock, RwLockPredicate,
};
use deko_std::wf::WellFormed;
use deko_std::{
    deko_bitflags, deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data, TrivialPredicate,
};
use uuid::Uuid;
use vstd::prelude::*;

use crate::collections::{update_vec, Vec};
use crate::cpu::irq::IrqSafeLockGuard;
use crate::cpu::regs::no_smap_zone;
use crate::cpu::task::{generate_id, DekoRunnableState};
use crate::cpu::DekoCpuCtx;
use crate::crypto::aes::aes_gcm_256_key_gen;
use crate::crypto::uuid::{generate_secure_uuid, uuid_print};
use crate::guest::service::{DekoNewAppReq, DekoNewAppType};
use crate::guest::{DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode, PtRegs};
use crate::mm::check_within_guest_mmap;
use crate::mm::frame_allocator::DekoAllocatorApi;
use crate::mm::paging::{bit_not_in_addr_region, strip_confidentiality_bits, PageTable};
use crate::mm::vm::TempMapping;
use crate::{kdebug, kerror, kinfo, kwarn, vec};

deko_bitflags! {
    pub struct DekoFile: u32 {
        const READ = 0;
        const WRITE = 1;
        const APPEND = 2;
    }
}

verus! {

pub exec static HOST_MNT_NS_ID: DekoSimpleRwLock<u64, IrqSafeLockGuard>
    ensures
        HOST_MNT_NS_ID.wf(),
{
    let r = DekoSimpleRwLock::new(
        DekoAtomicData::new(0),
        IrqSafeLockGuard {  },
        Ghost(TrivialPredicate::new()),
    );

    proof {
        use_type_invariant(&r);
    }

    r
}

pub type AppId = PhysAddr;

pub type DekoProcessMap = HashMap<AppId, DekoUserApp, DekoAllocatorApi>;

pub type DekoShimSet = HashMap<u32, (), DekoAllocatorApi>;

pub struct DekoShadowAppListPred;

pub struct DekoShimSetPred;

impl<P> RwLockPredicate<DekoAtomicData<Option<DekoProcessMap>, P>> for DekoShadowAppListPred {
    open spec fn inv(self, data: DekoAtomicData<Option<DekoProcessMap>, P>) -> bool {
        match data.data {
            Some(app_map) => app_map.wf(),
            None => true,
        }
    }
}

impl<P> RwLockPredicate<DekoAtomicData<Option<DekoShimSet>, P>> for DekoShimSetPred {
    open spec fn inv(self, data: DekoAtomicData<Option<DekoShimSet>, P>) -> bool {
        match data.data {
            Some(shim_set) => shim_set.wf(),
            None => true,
        }
    }
}

/// Tracks all currently running processes inside the guest VM that are spawned
/// by the container runtimes (e.g., runc, containerd) or are containerized applications.
///
/// The identifiers are the physical addresses of their main thread's CR3.
pub exec static DEKO_SHADOW_APP_LIST: DekoRwLock<
    Option<DekoProcessMap>,
    (),
    IrqSafeLockGuard,
    DekoShadowAppListPred,
>
    ensures
        DEKO_SHADOW_APP_LIST.wf(),
{
    let r = DekoRwLock::new(
        DekoAtomicData::new(None),
        IrqSafeLockGuard {  },
        Ghost(DekoShadowAppListPred {  }),
    );

    proof {
        use_type_invariant(&r);
    }

    r
}

pub exec static DEKO_SHIM_SET: DekoRwLock<
    Option<DekoShimSet>,
    (),
    IrqSafeLockGuard,
    DekoShimSetPred,
>
    ensures
        DEKO_SHIM_SET.wf(),
{
    let r = DekoRwLock::new(
        DekoAtomicData::new(None),
        IrqSafeLockGuard {  },
        Ghost(DekoShimSetPred {  }),
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

pub const DOCKER_INIT_NAME: &'static str = "docker-init";

pub const CONTAINERD_SHIM_NAME: &'static str = "containerd-shim";

pub const DOCKER_OVERLAY: &'static str = "overlay";

/// Checks whether the given file path is associated with Docker or container runtimes.
#[inline]
pub fn is_docker_request(path: &str) -> bool {
    path.contains(RUNC_NAME) || path.contains(CONTAINERD_NAME) || path.contains(
        CONTAINERD_SHIM_NAME,
    ) || path.contains(DOCKER_INIT_NAME) || path.contains(DOCKER_OVERLAY)
}

/// Checks whether the given parent PID belongs to a shim process.
pub fn lookup_parent_is_shim(ppid: u32) -> bool {
    deko_rwlock_read_atomic_data!(
        DEKO_SHIM_SET,
        shim_set,
        __,
        {
            match shim_set {
                Some(shim_set) => shim_set.contains_key(&ppid),
                None => false,
            }
        }
    )
}

/// Adds the given parent PID to the shim set.
pub fn add_to_shim_set(ppid: u32) {
    deko_rwlock_write_atomic_data!(
        DEKO_SHIM_SET,
        shim_set,
        __,
        {
            let mut new_shim_set = match shim_set {
                Some(set) => set,
                None => DekoShimSet::new_in(AllocatorWrapper(DekoAllocatorApi {  })),
            };

            new_shim_set.insert(ppid, ());

            shim_set = Some(new_shim_set);
        }
    )
}

pub fn remove_from_shim_set(ppid: u32) {
    deko_rwlock_write_atomic_data!(
        DEKO_SHIM_SET,
        shim_set,
        __,
        {
            if let Some(mut set) = shim_set {
                set.remove(&ppid);
                shim_set = Some(set);
            }
        }
    )
}

pub fn get_host_ns_id() -> DekoGuestServResult<u64> {
    let host_ns_id =
        deko_rwlock_read_atomic_data!(
        HOST_MNT_NS_ID,
        host_ns_lock,
        __,
        {
            *host_ns_lock
        }
    );

    if host_ns_id == 0 {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
    }
    Ok(host_ns_id)
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

/// The type of the shadowed user application.
#[derive(DekoDebug)]
pub struct DekoUserAppExt {
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

impl WellFormed for DekoUserAppExt {
    open spec fn wf(&self) -> bool {
        &&& forall|fd: u64|
            #![trigger self.opened_files@[fd]]
            self.opened_files@.contains_key(fd) ==> self.opened_files@[fd].wf()
        &&& forall|i: int|
            #![trigger self.occupied_regions@[i]]
            0 <= i < self.occupied_regions.len() ==> {
                &&& self.occupied_regions@[i].wf()
                &&& self.occupied_regions@[i].start@ % PAGE_SIZE == 0
                &&& self.occupied_regions@[i].end@
                    <= 0x8000_0000_0000  // Linux user-space limit

            }&&& self.measurement.len() == 48
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
    #[deko(hex)]
    pub container_id: u64,
    /// User ID (Effective UID).
    /// Used for basic privilege checks (is this root?).
    /// Maps to: task_struct->cred->euid
    pub uid: u32,
    // Deko Security Extensions.
    pub ext: DekoUserAppExt,
}

impl WellFormed for DekoUserApp {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.cr3@ % PAGE_SIZE == 0
        &&& self.cr3@ + PAGE_SIZE < 0x000f_ffff_ffff_f000u64
        &&& self.cr3.wf()
        &&& self.ext.wf()
    }
}

#[verus_verify]
impl DekoUserApp {
    /// Creates a new [`DekoUserApp`] with a unique id, an empty set of opened files,
    /// and a randomly generated AES-GCM-256 key.
    #[verus_spec(r =>
        requires
            app_req.wf(),
            guest_cr3.wf(),
            guest_cr3@ % PAGE_SIZE == 0,
            guest_cr3@ + PAGE_SIZE < 0x000f_ffff_ffff_f000u64,
            app_req.start_code@ > 0,
            app_req.start_code@ % PAGE_SIZE == 0,
            app_req.start_code@ < app_req.end_code@,
            app_req.end_code@ <= VADDR_LOWER_MASK, // Linux user-space limit
        ensures
            r matches Ok(r) ==> r.wf(),
    )]
    pub fn new(app_req: &DekoNewAppReq, guest_cr3: PhysAddr) -> DekoGuestServResult<Self> {
        let start_code = VirtAddr(app_req.start_code);
        let end_code = VirtAddr(app_req.end_code);
        let range = start_code..end_code;

        kinfo!("New app range is", range=>hex);

        let mut r = Self {
            pid: app_req.pid,
            tgid: app_req.tgid,
            parent_pid: app_req.ppid,
            uid: app_req.uid,
            container_id: app_req.mnt_ns_id,
            cr3: guest_cr3,
            ext: DekoUserAppExt {
                opened_files: HashMap::new_in(AllocatorWrapper(DekoAllocatorApi {  })),
                key: {
                    let mut key = [0u8;32];
                    aes_gcm_256_key_gen(&mut key);
                    key
                },
                occupied_regions: vec![],
                measurement: [0u8;48],
            },
        };

        r.add_and_measure(range)?;

        kinfo!("measurement is", r.ext.measurement);

        Ok(r)
    }

    /// Adds this memory region to the list of occupied regions
    /// and updates the measurement of the user application.
    #[verus_spec(r =>
        requires
            old(self).wf(),
            region.wf(),
            region.start@ > 0,
            region.start@ % PAGE_SIZE == 0,
            region.end@ <= VADDR_LOWER_MASK, // Linux user-space limit
        ensures
            self.wf(),
    )]
    pub fn add_and_measure(&mut self, region: VaddrRange) -> DekoGuestServResult<()> {
        let len = (region.end.0 - region.start.0 + PAGE_SIZE - 1) / PAGE_SIZE;
        let mut i = 0;
        let mut buf = vec![0u8; (PAGE_SIZE + 48) as usize];

        // Copy the hash to the buffer first.
        for j in 0..48
            invariant
                buf@.len() == (PAGE_SIZE + 48) as int,
                self.ext.measurement@.len() == 48,
                self.wf(),
        {
            update_vec(&mut buf, j, self.ext.measurement[j]);
        }

        #[verus_spec(
            invariant
                i <= len,
                buf@.len() == (PAGE_SIZE + 48) as int,
                len == (region.end@ - region.start@ + PAGE_SIZE - 1) / PAGE_SIZE as int,
                region.start@ > 0,
                region.end@ <= VADDR_LOWER_MASK,
                region.start@ % PAGE_SIZE == 0,
                PAGE_SIZE == 0x1000,
                VADDR_LOWER_MASK == 0x0000_7FFF_FFFF_FFFF,
                self.wf(),
            decreases
                len - i,
        )]
        while i < len {
            let cur = VirtAddr(region.start.0 + i * PAGE_SIZE);
            let remaining_bytes = region.end.0 - cur.0;
            let bytes_to_read = PAGE_SIZE.min(remaining_bytes) as usize;
            unsafe {
                copy_from_user(self.cr3, cur, buf.as_mut_ptr().add(48), bytes_to_read)?;
            }

            kdebug!("Reading page", cur=>hex, bytes_to_read=>hex);
            kdebug!("Content is:", buf);

            if bytes_to_read < PAGE_SIZE as usize {
                for k in bytes_to_read..(PAGE_SIZE as usize)
                    invariant
                        buf@.len() == (PAGE_SIZE + 48) as int,
                {
                    update_vec(&mut buf, 48 + k, 0);
                }
            }
            // Then we measure this page.
            //
            // This is a demo for now so the order does not matter and we
            // only care about the potential performance implications.
            //
            // For production-ready systems, we should consider using a Merkle tree
            // or other authenticated data structures to efficiently and securely
            // manage the measurements.

            let hash = crate::crypto::hash::sha3_384_hash(&buf);
            for j in 0..48
                invariant
                    buf@.len() == (PAGE_SIZE + 48) as int,
                    hash@.len() == 48,
                    self.wf(),
            {
                let b = hash[j];
                update_vec(&mut buf, j, b);
                self.ext.measurement[j] = b;
            }

            kdebug!("Measured page", cur=>hex, hash);

            i += 1;
        }

        Ok(())
    }

    /// Lifts the VMPL of the application's memory space to VMPL1.
    ///
    /// The default VMPL is the same as the guest kernel (VMPL2) but whenever there is
    /// a sensitive operation that receives the user's sensitive data (e.g., read from
    /// an encrypted socket), we need to lift the VMPL to VMPL1 to prevent the untrusted
    /// kernel from snooping on the data.
    ///
    /// This function does the thing by walking the page tables and updating the VMPL bits
    /// such that VMPL2 no longer has the read/write/execution permissions.
    #[verus_spec(r =>
        requires
            self.wf(),
    )]
    pub fn lift_vmpl(&self) -> DekoGuestServResult<()> {
        let cr3 = TempMapping::new(create_paddr_range(self.cr3, 1)).ok_or(
            DekoGuestServError::SoftError(DekoGuestServResultCode::Busy),
        )?;
        let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
        let private_bit = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).private_bit;
        let shared_bit = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).shared_bit;

        let s = self.ext.occupied_regions.len();
        for i in 0..s
            invariant
                s == self.ext.occupied_regions@.len(),
                self.wf(),
                cr3.wf(),
                cr3.inner.end@ - cr3.inner.start@ == PAGE_SIZE,
        {
            let cur = &self.ext.occupied_regions[i];
            let start = cur.start;
            let end = cur.end;
            let len = (end.0 - start.0 + PAGE_SIZE - 1) / PAGE_SIZE;
            let mut j = 0;

            #[verus_spec(
                invariant
                    j <= len,
                    cur == self.ext.occupied_regions@[i as int],
                    len == (end@ - start@ + PAGE_SIZE - 1) / PAGE_SIZE as int,
                    self.wf(),
                    cr3.wf(),
                    cr3.inner.end@ - cr3.inner.start@ == PAGE_SIZE,
                    PAGE_SIZE == 0x1000,
                decreases
                    len - j,
            )]
            while j < len {
                let va = VirtAddr(start.0 + j * PAGE_SIZE);
                // Look up the mapping.
                let mapping = PageTable::walk_lvl3_guest(&cr3, va, private_bit, shared_bit)?;
                if mapping.temp_mappings.len() <= 2 || mapping.temp_mappings.len() > 4 {
                    return Err(
                        DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam),
                    );
                }
                let final_mapping = mapping.final_mapping().unwrap();

                j += 1;
            }

        }

        Ok(())
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
        guest_cr3.wf(),
)]
pub fn register_user_app(
    req: &mut DekoNewAppReq,
    guest_cr3: PhysAddr,
    is_creation: bool,
) -> DekoGuestServResult<()> {
    // Check if the cr3 is valid in the current context.
    if core::hint::unlikely(!check_within_guest_mmap(guest_cr3) || guest_cr3.0 % PAGE_SIZE != 0) {
        kerror!("register_user_app: invalid guest CR3", guest_cr3);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let comm = req.comm;
    let comm = core::ffi::CStr::from_bytes_until_nul(&comm).map_err(
        |_e| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam),
    )?.to_str().map_err(|_e| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))?;

    if is_creation {
        do_reigster_user_app(req, comm, guest_cr3)
    } else {
        do_unregister_user_app(req, comm, guest_cr3)
    }
}

#[inline]
#[verus_spec(r =>
    ensures
        r == (req.start_code > 0 &&
            req.start_code % PAGE_SIZE == 0 &&
            req.start_code < req.end_code &&
            req.end_code <= VADDR_LOWER_MASK),
)]
fn check_user_vrange(req: &DekoNewAppReq) -> bool {
    req.start_code > 0 && req.start_code % PAGE_SIZE == 0 && req.start_code < req.end_code
        && req.end_code <= VADDR_LOWER_MASK
}

#[verus_spec(r =>
    requires
        guest_cr3.wf(),
        guest_cr3@ % PAGE_SIZE == 0,
)]
fn do_reigster_user_app(
    req: &mut DekoNewAppReq,
    comm: &str,
    guest_cr3: PhysAddr,
) -> DekoGuestServResult<()> {
    if core::hint::unlikely(
        guest_cr3.0 % PAGE_SIZE != 0 || guest_cr3.0 >= 0x000f_ffff_ffff_f000u64 - PAGE_SIZE,
    ) {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    match req.app_type {
        DekoNewAppType::DEKO_DOCKER_INFRA => {
            add_to_shim_set(req.pid);

            Ok(())
        },
        DekoNewAppType::DEKO_DOCKER_APPS => {
            // Look up if the parent is a shim process.
            if !lookup_parent_is_shim(req.ppid) {
                // Ignore.
                return Ok(());
            }
            if core::hint::unlikely(!check_user_vrange(req)) {
                kerror!("do_register_user_app: invalid user vaddr range", comm, req.start_code=>hex, req.end_code=>hex);
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
            }
            let user_app = DekoUserApp::new(req, guest_cr3)?;
            let new_user_uuid = generate_secure_uuid();
            uuid_print(&new_user_uuid);
            let (low, high) = new_user_uuid.as_u64_pair();
            req.token_low = low;
            req.token_high = high;

            deko_rwlock_write_atomic_data! {
                DEKO_SHADOW_APP_LIST,
                app_list,
                __,
                {
                    let mut napp_list = match app_list {
                        Some(mut ap) => ap,
                        None => DekoProcessMap::new_in(AllocatorWrapper(DekoAllocatorApi {  })),
                    };
                    let ghost old_napp_list = napp_list@;

                    napp_list.insert(guest_cr3, user_app);

                    proof {
                        assert(napp_list@ =~= old_napp_list.insert(guest_cr3, user_app));
                        assert(napp_list.wf()) by {
                            assert forall |k: AppId, v: DekoUserApp|
                                #[trigger] napp_list@.kv_pairs().contains((k, v)) implies k.wf() && v.wf() by {
                                    if old_napp_list.contains_key(k) {
                                        if k == guest_cr3 {
                                            broadcast use vstd::map::axiom_map_insert_same;
                                            assert(napp_list@[k] == user_app);
                                        } else {
                                            broadcast use vstd::map::axiom_map_insert_different;

                                            assert(old_napp_list.kv_pairs().contains((k, v)));
                                        }
                                    }
                                }
                        }
                    }

                    app_list = Some(napp_list);
                }
            }

            Ok(())
        },
        _ => Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam)),
    }
}

fn do_unregister_user_app(
    req: &DekoNewAppReq,
    comm: &str,
    guest_cr3: PhysAddr,
) -> DekoGuestServResult<()> {
    if req.pid == 1 {
        // Ignore /sbin/init exit: this means the guest is shutting down.
        return Ok(());
    }
    if is_docker_request(comm) {
        remove_from_shim_set(req.pid);

        return Ok(());
    }
    let is_docker_app = lookup_parent_is_shim(req.ppid);
    if is_docker_app {
        kinfo!("do_unregister_user_app: unregistering app", comm);

        deko_rwlock_write_atomic_data! {
        DEKO_SHADOW_APP_LIST,
        app_list,
        __,
        {
            let mut napp_list = match app_list {
                Some(mut ap) => ap,
                None => {
                    kinfo!("do_unregister_user_app: no apps registered");
                    HashMap::new_in(AllocatorWrapper(DekoAllocatorApi {  }))
                },
            };
            let ghost old_napp_list = napp_list@;
            napp_list.remove(&guest_cr3);
            proof {
                assert(napp_list@ =~= old_napp_list.remove(guest_cr3));
                assert(napp_list.wf()) by {
                    assert forall |k: AppId, v: DekoUserApp|
                        #[trigger] napp_list@.kv_pairs().contains((k, v)) implies k.wf() && v.wf() by {
                            if napp_list@.contains_key(k) {
                                assert(old_napp_list.kv_pairs().contains((k, v)));
                            }
                        }
                }
            }
            app_list = Some(napp_list);
        }
    }
    }
    Ok(())
}

/// Try to kick the applications in the guest VM to VMPL1.
///
/// This function never returns!
#[verus_spec()]
#[verifier::exec_allows_no_decreases_clause]
pub fn try_kick_app(regs: &PtRegs) -> ! {
    // Reconstruct the UUID from the registers.
    let token_low = regs.cx;
    let token_high = regs.dx;
    let uuid = Uuid::from_u64_pair(token_low, token_high);

    uuid_print(&uuid);

    kinfo!("placeholder. loop now");

    loop {
    }
}

} // verus!
