#[cfg(feature = "alloc")]
use deko_std::wf::WellFormed;
use vstd::prelude::*;

#[cfg(feature = "alloc")]
use crate::collections::Vec;
#[cfg(feature = "alloc")]
use crate::guest::{DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode};
#[cfg(feature = "alloc")]
use crate::policy::lattice::LatticeConfigToml;

verus! {

#[cfg(feature = "alloc")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolicyConfigToml {
    pub lattice: LatticeConfigToml,
}

#[cfg(feature = "alloc")]
impl WellFormed for PolicyConfigToml {
    open spec fn wf(&self) -> bool {
        self.lattice.wf()
    }
}

#[cfg(feature = "alloc")]
/// Trusted parser boundary: this function may use unsupported serde/toml
/// machinery internally, but it must only return well-formed policy values.
#[verifier::external_body]
#[verus_spec(r =>
    ensures
        r matches Ok(policy) ==> policy.wf(),
)]
pub fn parse_policy_config_from_bytes(buf: &[u8]) -> DekoGuestServResult<PolicyConfigToml> {
    #[derive(serde::Deserialize)]
    struct RawPolicyConfigToml {
        lattice: RawLatticeConfigToml,
    }

    #[derive(serde::Deserialize)]
    struct RawLatticeConfigToml {
        levels: alloc::vec::Vec<alloc::string::String>,
        relations: alloc::vec::Vec<[alloc::string::String; 2]>,
        bot: alloc::string::String,
        top: alloc::string::String,
    }

    fn bytes_from_str(s: &str) -> Vec<u8> {
        let bytes = s.as_bytes();
        let mut out = Vec::with_capacity_in(
            bytes.len(),
            crate::mm::frame_allocator::DekoAllocatorApi {  },
        );
        for b in bytes {
            out.push(*b);
        }
        out
    }

    fn lattice_from_raw(raw: RawLatticeConfigToml) -> LatticeConfigToml {
        let mut levels = Vec::with_capacity_in(
            raw.levels.len(),
            crate::mm::frame_allocator::DekoAllocatorApi {  },
        );
        for level in raw.levels {
            levels.push(bytes_from_str(level.as_str()));
        }

        let mut relations = Vec::with_capacity_in(
            raw.relations.len(),
            crate::mm::frame_allocator::DekoAllocatorApi {  },
        );
        for relation in raw.relations {
            let [lhs, rhs] = relation;
            relations.push((bytes_from_str(lhs.as_str()), bytes_from_str(rhs.as_str())));
        }

        LatticeConfigToml {
            levels,
            relations,
            bot: bytes_from_str(raw.bot.as_str()),
            top: bytes_from_str(raw.top.as_str()),
        }
    }

    let content = core::str::from_utf8(buf).map_err(
        |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
    )?;
    let raw = toml::from_str::<RawPolicyConfigToml>(content).map_err(
        |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
    )?;
    Ok(PolicyConfigToml { lattice: lattice_from_raw(raw.lattice) })
}

} // verus!
