#[cfg(feature = "alloc")]
use deko_policy_format::{
    decode_borrowed_lattice_v1_blob, decode_policy_blob_header, PolicyBlobKind, POLICY_FORMAT_MAGIC,
};
#[cfg(feature = "alloc")]
use deko_std::wf::WellFormed;
use vstd::prelude::*;

#[cfg(feature = "alloc")]
use crate::collections::Vec;
#[cfg(feature = "alloc")]
use crate::guest::{DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode};
#[cfg(feature = "alloc")]
use crate::kinfo;
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
    fn bytes_from_slice(s: &[u8]) -> Vec<u8> {
        let mut out = Vec::with_capacity_in(
            s.len(),
            crate::mm::frame_allocator::DekoAllocatorApi {  },
        );
        for b in s {
            out.push(*b);
        }
        out
    }

    fn try_parse_binary_policy(buf: &[u8]) -> DekoGuestServResult<Option<PolicyConfigToml>> {
        if buf.len() < 4 {
            return Ok(None);
        }
        let magic = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
        if magic != POLICY_FORMAT_MAGIC {
            return Ok(None);
        }
        let (header, payload) = decode_policy_blob_header(buf).map_err(
            |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
        )?;
        kinfo!(
            "Policy blob header: buf_len=",
            buf.len(),
            " payload_len=",
            header.payload_len,
            " kind=",
            header.kind,
            " version=",
            header.version,
        );
        if header.kind != PolicyBlobKind::LatticeV1 as u16 {
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat));
        }
        let blob = decode_borrowed_lattice_v1_blob(payload).map_err(
            |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
        )?;
        kinfo!(
            "Policy lattice header: level_count=",
            blob.header.level_count,
            " relation_count=",
            blob.header.relation_count,
            " string_bytes_len=",
            blob.header.string_bytes_len,
            " bot_idx=",
            blob.header.bot_level_idx,
            " top_idx=",
            blob.header.top_level_idx,
        );

        let mut levels = Vec::with_capacity_in(
            blob.header.level_count as usize,
            crate::mm::frame_allocator::DekoAllocatorApi {  },
        );
        let mut i = 0;
        while i < blob.header.level_count {
            let level_bytes = blob.level_bytes(i).map_err(
                |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
            )?;
            levels.push(bytes_from_slice(level_bytes));
            i += 1;
        }

        let mut relations = Vec::with_capacity_in(
            blob.header.relation_count as usize,
            crate::mm::frame_allocator::DekoAllocatorApi {  },
        );
        let mut j = 0;
        while j < blob.header.relation_count {
            let rel = blob.relation_ref(j).map_err(
                |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
            )?;
            let lhs = blob.level_bytes(rel.lhs_level_idx).map_err(
                |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
            )?;
            let rhs = blob.level_bytes(rel.rhs_level_idx).map_err(
                |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
            )?;
            relations.push((bytes_from_slice(lhs), bytes_from_slice(rhs)));
            j += 1;
        }

        let bot = bytes_from_slice(
            blob.level_bytes(blob.header.bot_level_idx).map_err(
                |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
            )?,
        );
        let top = bytes_from_slice(
            blob.level_bytes(blob.header.top_level_idx).map_err(
                |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
            )?,
        );

        Ok(Some(PolicyConfigToml { lattice: LatticeConfigToml { levels, relations, bot, top } }))
    }

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
        bytes_from_slice(s.as_bytes())
    }

    if let Some(policy) = try_parse_binary_policy(buf)? {
        return Ok(policy);
    }
    let content = core::str::from_utf8(buf).map_err(
        |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
    )?;
    let raw = toml::from_str::<RawPolicyConfigToml>(content).map_err(
        |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
    )?;
    let mut raw_level_bytes = Vec::with_capacity_in(
        raw.lattice.levels.len(),
        crate::mm::frame_allocator::DekoAllocatorApi {  },
    );
    for level in raw.lattice.levels.iter() {
        raw_level_bytes.push(bytes_from_str(level.as_str()));
    }
    let mut raw_relation_bytes = Vec::with_capacity_in(
        raw.lattice.relations.len(),
        crate::mm::frame_allocator::DekoAllocatorApi {  },
    );
    for relation in raw.lattice.relations.iter() {
        raw_relation_bytes.push(
            (bytes_from_str(relation[0].as_str()), bytes_from_str(relation[1].as_str())),
        );
    }
    let raw_bot_bytes = bytes_from_str(raw.lattice.bot.as_str());
    let raw_top_bytes = bytes_from_str(raw.lattice.top.as_str());
    let lattice = LatticeConfigToml {
        levels: raw_level_bytes,
        relations: raw_relation_bytes,
        bot: raw_bot_bytes,
        top: raw_top_bytes,
    };
    Ok(PolicyConfigToml { lattice })
}

} // verus!
