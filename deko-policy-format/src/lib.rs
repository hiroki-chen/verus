#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use deko_std::prelude::*;
use vstd::prelude::*;

verus! {

pub const POLICY_FORMAT_MAGIC: u32 = 0x444B_5046;

pub const POLICY_FORMAT_VERSION: u16 = 1;

pub const LATTICE_V1_HEADER_SIZE: u32 = 32;

pub const LATTICE_V1_LEVEL_ENTRY_SIZE: u32 = 8;

pub const LATTICE_V1_RELATION_ENTRY_SIZE: u32 = 8;

#[repr(u16)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolicyBlobKind {
    LatticeV1 = 1,
    FullPolicyV1 = 2,
}

impl WellFormed for PolicyBlobKind {
    open spec fn wf(&self) -> bool {
        true
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolicyBlobHeader {
    pub magic: u32,
    pub version: u16,
    pub kind: u16,
    pub payload_len: u32,
}

impl PolicyBlobHeader {
    #[verifier::inline]
    pub open spec fn kind_supported_spec(&self) -> bool {
        self.kind == PolicyBlobKind::LatticeV1 as u16 || self.kind
            == PolicyBlobKind::FullPolicyV1 as u16
    }
}

impl WellFormed for PolicyBlobHeader {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.magic == POLICY_FORMAT_MAGIC
        &&& self.version == POLICY_FORMAT_VERSION
        &&& self.kind_supported_spec()
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LatticeV1Header {
    pub level_count: u32,
    pub relation_count: u32,
    pub level_table_offset: u32,
    pub relation_table_offset: u32,
    pub string_bytes_offset: u32,
    pub string_bytes_len: u32,
    pub bot_level_idx: u32,
    pub top_level_idx: u32,
}

impl LatticeV1Header {
    #[verifier::inline]
    pub open spec fn level_table_end_spec(&self) -> nat {
        self.level_table_offset as nat + self.level_count as nat
            * LATTICE_V1_LEVEL_ENTRY_SIZE as nat
    }

    #[verifier::inline]
    pub open spec fn relation_table_end_spec(&self) -> nat {
        self.relation_table_offset as nat + self.relation_count as nat
            * LATTICE_V1_RELATION_ENTRY_SIZE as nat
    }

    #[verifier::inline]
    pub open spec fn string_bytes_end_spec(&self) -> nat {
        self.string_bytes_offset as nat + self.string_bytes_len as nat
    }
}

impl WellFormed for LatticeV1Header {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.level_table_offset >= LATTICE_V1_HEADER_SIZE
        &&& self.relation_table_offset >= self.level_table_offset
        &&& self.string_bytes_offset >= self.relation_table_offset
        &&& self.bot_level_idx < self.level_count
        &&& self.top_level_idx < self.level_count
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LatticeV1StringRef {
    pub offset: u32,
    pub len: u32,
}

impl WellFormed for LatticeV1StringRef {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LatticeV1RelationRef {
    pub lhs_level_idx: u32,
    pub rhs_level_idx: u32,
}

impl WellFormed for LatticeV1RelationRef {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolicyFormatDecodeError {
    BufferTooShort,
    InvalidMagic,
    InvalidVersion,
    InvalidKind,
    InvalidLength,
    InvalidOffset,
    IntegerOverflow,
}

impl WellFormed for PolicyFormatDecodeError {
    open spec fn wf(&self) -> bool {
        true
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolicyFormatEncodeError {
    InvalidLevelCount,
    InvalidLevelIndex,
    IntegerOverflow,
}

impl WellFormed for PolicyFormatEncodeError {
    open spec fn wf(&self) -> bool {
        true
    }
}

#[cfg(feature = "alloc")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowedPolicyBlob<'a> {
    pub header: PolicyBlobHeader,
    pub payload: &'a [u8],
}

#[cfg(feature = "alloc")]
impl<'a> WellFormed for BorrowedPolicyBlob<'a> {
    open spec fn wf(&self) -> bool {
        &&& self.header.wf()
        &&& self.payload@.len() == self.header.payload_len as nat
    }
}

#[cfg(feature = "alloc")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowedLatticeV1Blob<'a> {
    pub header: LatticeV1Header,
    pub level_table_bytes: &'a [u8],
    pub relation_table_bytes: &'a [u8],
    pub string_bytes: &'a [u8],
}

#[cfg(feature = "alloc")]
impl<'a> BorrowedLatticeV1Blob<'a> {
    #[verifier::inline]
    pub open spec fn level_count_spec(&self) -> nat {
        self.header.level_count as nat
    }

    #[verifier::inline]
    pub open spec fn relation_count_spec(&self) -> nat {
        self.header.relation_count as nat
    }

    pub fn level_ref(&self, idx: u32) -> Result<LatticeV1StringRef, PolicyFormatDecodeError> {
        if idx >= self.header.level_count {
            return Err(PolicyFormatDecodeError::InvalidOffset);
        }
        decode_string_ref_entry(self.level_table_bytes, idx)
    }

    pub fn relation_ref(&self, idx: u32) -> Result<LatticeV1RelationRef, PolicyFormatDecodeError> {
        if idx >= self.header.relation_count {
            return Err(PolicyFormatDecodeError::InvalidOffset);
        }
        decode_relation_ref_entry(self.relation_table_bytes, idx)
    }

    pub fn level_bytes(&self, idx: u32) -> Result<&'a [u8], PolicyFormatDecodeError> {
        let level = self.level_ref(idx)?;
        subslice(self.string_bytes, level.offset, level.len)
    }
}

#[cfg(feature = "alloc")]
impl<'a> WellFormed for BorrowedLatticeV1Blob<'a> {
    open spec fn wf(&self) -> bool {
        &&& self.header.wf()
        &&& self.level_table_bytes@.len() == self.header.level_count as nat
            * LATTICE_V1_LEVEL_ENTRY_SIZE as nat
        &&& self.relation_table_bytes@.len() == self.header.relation_count as nat
            * LATTICE_V1_RELATION_ENTRY_SIZE as nat
        &&& self.string_bytes@.len() == self.header.string_bytes_len as nat
    }
}

#[cfg(feature = "alloc")]
fn checked_add_u32(lhs: u32, rhs: u32) -> Result<u32, PolicyFormatDecodeError> {
    lhs.checked_add(rhs).ok_or(PolicyFormatDecodeError::IntegerOverflow)
}

#[cfg(feature = "alloc")]
fn checked_mul_u32(lhs: u32, rhs: u32) -> Result<u32, PolicyFormatDecodeError> {
    lhs.checked_mul(rhs).ok_or(PolicyFormatDecodeError::IntegerOverflow)
}

#[cfg(feature = "alloc")]
fn checked_add_u32_encode(lhs: u32, rhs: u32) -> Result<u32, PolicyFormatEncodeError> {
    lhs.checked_add(rhs).ok_or(PolicyFormatEncodeError::IntegerOverflow)
}

#[cfg(feature = "alloc")]
fn checked_mul_u32_encode(lhs: u32, rhs: u32) -> Result<u32, PolicyFormatEncodeError> {
    lhs.checked_mul(rhs).ok_or(PolicyFormatEncodeError::IntegerOverflow)
}

#[cfg(feature = "alloc")]
fn push_u16_le(out: &mut Vec<u8>, value: u16) {
    out.push((value & 0x00ff) as u8);
    out.push((value >> 8) as u8);
}

#[cfg(feature = "alloc")]
fn push_u32_le(out: &mut Vec<u8>, value: u32) {
    out.push((value & 0x0000_00ff) as u8);
    out.push(((value >> 8) & 0x0000_00ff) as u8);
    out.push(((value >> 16) & 0x0000_00ff) as u8);
    out.push(((value >> 24) & 0x0000_00ff) as u8);
}

#[cfg(feature = "alloc")]
pub fn encode_lattice_v1_blob(
    levels: &[&[u8]],
    relations: &[(u32, u32)],
    bot_level_idx: u32,
    top_level_idx: u32,
) -> Result<Vec<u8>, PolicyFormatEncodeError> {
    let level_count = levels.len() as u32;
    let relation_count = relations.len() as u32;
    if level_count == 0 {
        return Err(PolicyFormatEncodeError::InvalidLevelCount);
    }
    if bot_level_idx >= level_count || top_level_idx >= level_count {
        return Err(PolicyFormatEncodeError::InvalidLevelIndex);
    }
    let mut rel_idx = 0usize;
    while rel_idx < relations.len()
        decreases relations.len() - rel_idx,
    {
        let (lhs, rhs) = relations[rel_idx];
        if lhs >= level_count || rhs >= level_count {
            return Err(PolicyFormatEncodeError::InvalidLevelIndex);
        }
        rel_idx += 1;
    }

    let level_table_offset = LATTICE_V1_HEADER_SIZE;
    let level_table_len = checked_mul_u32_encode(level_count, LATTICE_V1_LEVEL_ENTRY_SIZE)?;
    let relation_table_offset = checked_add_u32_encode(level_table_offset, level_table_len)?;
    let relation_table_len = checked_mul_u32_encode(
        relation_count,
        LATTICE_V1_RELATION_ENTRY_SIZE,
    )?;
    let string_bytes_offset = checked_add_u32_encode(relation_table_offset, relation_table_len)?;

    let mut string_bytes_len = 0u32;
    let mut level_idx = 0usize;
    while level_idx < levels.len()
        decreases levels.len() - level_idx,
    {
        string_bytes_len =
        checked_add_u32_encode(string_bytes_len, levels[level_idx].len() as u32)?;
        level_idx += 1;
    }

    let mut payload = Vec::new();
    push_u32_le(&mut payload, level_count);
    push_u32_le(&mut payload, relation_count);
    push_u32_le(&mut payload, level_table_offset);
    push_u32_le(&mut payload, relation_table_offset);
    push_u32_le(&mut payload, string_bytes_offset);
    push_u32_le(&mut payload, string_bytes_len);
    push_u32_le(&mut payload, bot_level_idx);
    push_u32_le(&mut payload, top_level_idx);

    let mut running_offset = 0u32;
    let mut level_ref_idx = 0usize;
    while level_ref_idx < levels.len()
        decreases levels.len() - level_ref_idx,
    {
        let level = levels[level_ref_idx];
        push_u32_le(&mut payload, running_offset);
        push_u32_le(&mut payload, level.len() as u32);
        running_offset = checked_add_u32_encode(running_offset, level.len() as u32)?;
        level_ref_idx += 1;
    }

    let mut relation_ref_idx = 0usize;
    while relation_ref_idx < relations.len()
        decreases relations.len() - relation_ref_idx,
    {
        let (lhs, rhs) = relations[relation_ref_idx];
        push_u32_le(&mut payload, lhs);
        push_u32_le(&mut payload, rhs);
        relation_ref_idx += 1;
    }

    let mut string_idx = 0usize;
    while string_idx < levels.len()
        decreases levels.len() - string_idx,
    {
        payload.extend_from_slice(levels[string_idx]);
        string_idx += 1;
    }

    let mut blob = Vec::new();
    push_u32_le(&mut blob, POLICY_FORMAT_MAGIC);
    push_u16_le(&mut blob, POLICY_FORMAT_VERSION);
    push_u16_le(&mut blob, PolicyBlobKind::LatticeV1 as u16);
    push_u32_le(&mut blob, payload.len() as u32);
    blob.extend_from_slice(payload.as_slice());
    Ok(blob)
}

#[cfg(feature = "alloc")]
fn subslice<'a>(buf: &'a [u8], offset: u32, len: u32) -> Result<&'a [u8], PolicyFormatDecodeError> {
    let end = checked_add_u32(offset, len)?;
    buf.get(offset as usize..end as usize).ok_or(PolicyFormatDecodeError::InvalidOffset)
}

#[cfg(feature = "alloc")]
fn read_u16_le(buf: &[u8], offset: usize) -> Result<u16, PolicyFormatDecodeError> {
    let b0 = *buf.get(offset).ok_or(PolicyFormatDecodeError::BufferTooShort)?;
    let b1 = *buf.get(offset + 1).ok_or(PolicyFormatDecodeError::BufferTooShort)?;
    Ok((b0 as u16) | ((b1 as u16) << 8))
}

#[cfg(feature = "alloc")]
fn read_u32_le(buf: &[u8], offset: usize) -> Result<u32, PolicyFormatDecodeError> {
    let b0 = *buf.get(offset).ok_or(PolicyFormatDecodeError::BufferTooShort)?;
    let b1 = *buf.get(offset + 1).ok_or(PolicyFormatDecodeError::BufferTooShort)?;
    let b2 = *buf.get(offset + 2).ok_or(PolicyFormatDecodeError::BufferTooShort)?;
    let b3 = *buf.get(offset + 3).ok_or(PolicyFormatDecodeError::BufferTooShort)?;
    Ok((b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24))
}

#[cfg(feature = "alloc")]
fn decode_string_ref_entry(table_bytes: &[u8], idx: u32) -> Result<
    LatticeV1StringRef,
    PolicyFormatDecodeError,
> {
    let base = checked_mul_u32(idx, LATTICE_V1_LEVEL_ENTRY_SIZE)? as usize;
    Ok(
        LatticeV1StringRef {
            offset: read_u32_le(table_bytes, base)?,
            len: read_u32_le(table_bytes, base + 4)?,
        },
    )
}

#[cfg(feature = "alloc")]
fn decode_relation_ref_entry(table_bytes: &[u8], idx: u32) -> Result<
    LatticeV1RelationRef,
    PolicyFormatDecodeError,
> {
    let base = checked_mul_u32(idx, LATTICE_V1_RELATION_ENTRY_SIZE)? as usize;
    Ok(
        LatticeV1RelationRef {
            lhs_level_idx: read_u32_le(table_bytes, base)?,
            rhs_level_idx: read_u32_le(table_bytes, base + 4)?,
        },
    )
}

#[cfg(feature = "alloc")]
pub fn decode_policy_blob_header(buf: &[u8]) -> Result<
    (PolicyBlobHeader, &[u8]),
    PolicyFormatDecodeError,
> {
    if buf.len() < 12 {
        return Err(PolicyFormatDecodeError::BufferTooShort);
    }
    let header = PolicyBlobHeader {
        magic: read_u32_le(buf, 0)?,
        version: read_u16_le(buf, 4)?,
        kind: read_u16_le(buf, 6)?,
        payload_len: read_u32_le(buf, 8)?,
    };
    if header.magic != POLICY_FORMAT_MAGIC {
        return Err(PolicyFormatDecodeError::InvalidMagic);
    }
    if header.version != POLICY_FORMAT_VERSION {
        return Err(PolicyFormatDecodeError::InvalidVersion);
    }
    if header.kind != PolicyBlobKind::LatticeV1 as u16 && header.kind
        != PolicyBlobKind::FullPolicyV1 as u16 {
        return Err(PolicyFormatDecodeError::InvalidKind);
    }
    if buf.len() < 12 + header.payload_len as usize {
        return Err(PolicyFormatDecodeError::InvalidLength);
    }
    let payload = buf.get(12..12 + header.payload_len as usize).ok_or(
        PolicyFormatDecodeError::InvalidLength,
    )?;
    Ok((header, payload))
}

#[cfg(feature = "alloc")]
pub fn decode_lattice_v1_header(buf: &[u8]) -> Result<LatticeV1Header, PolicyFormatDecodeError> {
    if buf.len() < LATTICE_V1_HEADER_SIZE as usize {
        return Err(PolicyFormatDecodeError::BufferTooShort);
    }
    let header = LatticeV1Header {
        level_count: read_u32_le(buf, 0)?,
        relation_count: read_u32_le(buf, 4)?,
        level_table_offset: read_u32_le(buf, 8)?,
        relation_table_offset: read_u32_le(buf, 12)?,
        string_bytes_offset: read_u32_le(buf, 16)?,
        string_bytes_len: read_u32_le(buf, 20)?,
        bot_level_idx: read_u32_le(buf, 24)?,
        top_level_idx: read_u32_le(buf, 28)?,
    };
    if !(header.level_table_offset >= LATTICE_V1_HEADER_SIZE && header.relation_table_offset
        >= header.level_table_offset && header.string_bytes_offset >= header.relation_table_offset
        && header.bot_level_idx < header.level_count && header.top_level_idx < header.level_count) {
        return Err(PolicyFormatDecodeError::InvalidOffset);
    }
    Ok(header)
}

#[cfg(feature = "alloc")]
pub fn decode_borrowed_lattice_v1_blob(buf: &[u8]) -> Result<
    BorrowedLatticeV1Blob<'_>,
    PolicyFormatDecodeError,
> {
    let header = decode_lattice_v1_header(buf)?;
    let level_table_len = checked_mul_u32(header.level_count, LATTICE_V1_LEVEL_ENTRY_SIZE)?;
    let relation_table_len = checked_mul_u32(
        header.relation_count,
        LATTICE_V1_RELATION_ENTRY_SIZE,
    )?;
    let level_table_end = checked_add_u32(header.level_table_offset, level_table_len)?;
    let relation_table_end = checked_add_u32(header.relation_table_offset, relation_table_len)?;
    let string_bytes_end = checked_add_u32(header.string_bytes_offset, header.string_bytes_len)?;
    if !(header.level_table_offset <= level_table_end && level_table_end
        <= header.relation_table_offset && header.relation_table_offset <= relation_table_end
        && relation_table_end <= header.string_bytes_offset && header.string_bytes_offset
        <= string_bytes_end && string_bytes_end as usize <= buf.len()) {
        return Err(PolicyFormatDecodeError::InvalidOffset);
    }
    let borrowed = BorrowedLatticeV1Blob {
        header,
        level_table_bytes: subslice(buf, header.level_table_offset, level_table_len)?,
        relation_table_bytes: subslice(buf, header.relation_table_offset, relation_table_len)?,
        string_bytes: subslice(buf, header.string_bytes_offset, header.string_bytes_len)?,
    };
    if !(borrowed.level_table_bytes.len() == header.level_count as usize
        * LATTICE_V1_LEVEL_ENTRY_SIZE as usize && borrowed.relation_table_bytes.len()
        == header.relation_count as usize * LATTICE_V1_RELATION_ENTRY_SIZE as usize
        && borrowed.string_bytes.len() == header.string_bytes_len as usize) {
        return Err(PolicyFormatDecodeError::InvalidLength);
    }
    Ok(borrowed)
}

} // verus!
