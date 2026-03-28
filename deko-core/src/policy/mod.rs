use deko_macros::DekoDebug;
use deko_std::address::VirtAddr;
#[cfg(feature = "alloc")]
use deko_std::prelude::collections::hashmap::HashMap;
#[cfg(feature = "alloc")]
use deko_std::std_extra::allocator::AllocatorWrapper;
#[cfg(feature = "alloc")]
use deko_std::sync::{DekoAtomicData, DekoRwLock, RwLockPredicate};
use deko_std::wf::WellFormed;
use deko_std::with_permission;
use vstd::prelude::*;

#[cfg(feature = "alloc")]
use crate::cpu::irq::IrqSafeLockGuard;
use crate::guest::{DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode};
use crate::kerror;
#[cfg(feature = "alloc")]
use crate::kinfo;
#[cfg(feature = "alloc")]
use crate::mm::frame_allocator::DekoAllocatorApi;
use crate::policy::userapp::setup_vmpl1_func_ptr;
#[cfg(feature = "alloc")]
use crate::{deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data, TrivialPredicate};

pub(crate) mod config;
pub(crate) mod fs;
pub(crate) mod ifc;
pub(crate) mod lattice;
pub(crate) mod mapping;
pub(crate) mod syscall;
pub(crate) mod userapp;

#[cfg(feature = "alloc")]
pub use config::PolicyConfigToml;

pub use crate::mm::paging::RECURSIVE_INDEX;

verus! {

#[cfg(feature = "alloc")]
pub type DomainId = u32;

#[cfg(feature = "alloc")]
pub type DekoPolicyDomainMap = HashMap<DomainId, DekoPolicyDomain, DekoAllocatorApi>;

global layout DekoSyscallBody is size == 0x50;

/// The policy engine is responsible for enforcing security policies.
#[derive(DekoDebug)]
pub struct DekoPolicyEngine {
    #[cfg(feature = "alloc")]
    #[deko(skip)]
    domains: DekoPolicyDomainMap,
    #[cfg(feature = "alloc")]
    pub default_domain: Option<DomainId>,
}

/// A policy domain represents a security boundary within which certain
/// policies are enforced.
#[derive(DekoDebug)]
pub struct DekoPolicyDomain {
    #[cfg(feature = "alloc")]
    pub domain_id: DomainId,
    #[cfg(feature = "alloc")]
    #[deko(skip)]
    pub policy: config::PolicyConfigToml,
    #[cfg(feature = "alloc")]
    #[deko(skip)]
    pub lattice: lattice::FiniteLattice,
}

#[cfg(feature = "alloc")]
impl WellFormed for DekoPolicyDomain {
    open spec fn wf(&self) -> bool {
        self.policy.wf() && self.lattice.wf()
    }
}

#[cfg(feature = "alloc")]
pub struct DekoPolicyEnginePred;

#[cfg(feature = "alloc")]
impl<P> RwLockPredicate<DekoAtomicData<Option<DekoPolicyEngine>, P>> for DekoPolicyEnginePred {
    open spec fn inv(self, data: DekoAtomicData<Option<DekoPolicyEngine>, P>) -> bool {
        match data.data {
            Some(engine) => engine.wf(),
            None => true,
        }
    }
}

#[cfg(feature = "alloc")]
pub exec static DEKO_POLICY_ENGINE: DekoRwLock<
    Option<DekoPolicyEngine>,
    (),
    IrqSafeLockGuard,
    DekoPolicyEnginePred,
>
    ensures
        DEKO_POLICY_ENGINE.wf(),
{
    let r = DekoRwLock::new(
        DekoAtomicData::new(None),
        IrqSafeLockGuard {  },
        Ghost(DekoPolicyEnginePred {  }),
    );

    proof {
        use_type_invariant(&r);
    }

    r
}

#[verus_verify]
impl DekoPolicyEngine {
    #[cfg(feature = "alloc")]
    pub closed spec fn wf(&self) -> bool {
        &&& self.domains.wf()
        &&& (self.default_domain is Some ==> self.domains@.contains_key(
            self.default_domain.unwrap(),
        ))
    }

    #[cfg(feature = "alloc")]
    #[verus_spec(r =>
        ensures
            r.wf(),
            r.domains@ =~= Map::<DomainId, DekoPolicyDomain>::empty(),
            r.default_domain is None,
    )]
    fn new() -> Self {
        Self {
            domains: HashMap::new_in(AllocatorWrapper(DekoAllocatorApi {  })),
            default_domain: None,
        }
    }

    #[cfg(feature = "alloc")]
    #[verus_spec(r =>
        requires
            old(self).wf(),
        ensures
            self.wf(),
    )]
    fn load_domain_from_bytes(&mut self, domain_id: DomainId, buf: &[u8]) -> DekoGuestServResult<
        (),
    > {
        let policy = config::parse_policy_config_from_bytes(buf)?;
        let lattice = lattice::FiniteLattice::compile(&policy.lattice).map_err(
            |err|
                {
                    kerror!("Failed to compile lattice for domain_id=", domain_id, ": ", err);
                    DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat)
                },
        )?;
        self.domains.insert(domain_id, DekoPolicyDomain { domain_id, policy, lattice });
        if self.default_domain.is_none() {
            self.default_domain = Some(domain_id);
        }
        Ok(())
    }

    /// Initializes the policy engine from a byte buffer that contains the TOML
    /// configuration for the policies.
    #[cfg(feature = "alloc")]
    #[verus_spec(r =>
        ensures
            r matches Ok(engine) ==> engine.wf(),
    )]
    pub fn init_from_bytes(buf: &[u8]) -> DekoGuestServResult<Self> {
        let mut engine = Self::new();
        engine.load_domain_from_bytes(0, buf)?;
        Ok(engine)
    }

    /// Returns the compiled lattice of the default policy domain, if one has
    /// already been loaded into the engine.
    #[cfg(feature = "alloc")]
    pub fn default_lattice(&self) -> Option<&lattice::FiniteLattice> {
        match self.default_domain {
            Some(domain_id) => self.domains.get(&domain_id).map(|domain| &domain.lattice),
            None => None,
        }
    }
}

with_permission!(
    DekoPolicyDomain,
);

#[cfg(feature = "alloc")]
pub fn register_policy_domain(domain_id: DomainId, buf: &[u8]) -> DekoGuestServResult<()> {
    deko_rwlock_write_atomic_data!(
        DEKO_POLICY_ENGINE,
        engine_state,
        __,
        {
            let mut engine = match engine_state.take() {
                Some(engine) => engine,
                None => DekoPolicyEngine::new(),
            };
            let load_result = engine.load_domain_from_bytes(domain_id, buf);
            engine_state = Some(engine);
            load_result
        }
    )
}

#[cfg(feature = "alloc")]
pub fn policy_domain_exists(domain_id: DomainId) -> bool {
    deko_rwlock_read_atomic_data!(
        DEKO_POLICY_ENGINE,
        engine_state,
        __,
        {
            match engine_state {
                Some(engine) => engine.domains.contains_key(&domain_id),
                None => false,
            }
        }
    )
}

#[repr(C, align(8))]
#[derive(DekoDebug, Clone, Copy)]
pub struct DekoSyscallBody {
    #[deko(hex)]
    pub rax: u64,  // Syscall number
    #[deko(hex)]
    pub rdi: u64,  // Arg 1
    #[deko(hex)]
    pub rsi: u64,  // Arg 2
    #[deko(hex)]
    pub rdx: u64,  // Arg 3
    #[deko(hex)]
    pub r10: u64,  // Arg 4
    #[deko(hex)]
    pub r8: u64,  // Arg 5
    #[deko(hex)]
    pub r9: u64,  // Arg 6
    #[deko(hex)]
    pub rcx: u64,  // Return Address
    #[deko(hex)]
    pub r11: u64,  // RFLAG
    // The current cr3.
    #[deko(hex)]
    pub cr3: u64,
}

impl WellFormed for DekoSyscallBody {
    open spec fn wf(&self) -> bool {
        true
    }
}

} // verus!
