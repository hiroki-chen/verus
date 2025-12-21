use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::array::Array;
use deko_std::mem::PAGE_SIZE;
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::sync::{DekoAtomicData, DekoOnceCell, DekoSimpleOnceCell};
use deko_std::wf::WellFormed;
use deko_std::{boxed_ptr, with_permission};
use vstd::prelude::*;

use crate::kinfo;
use crate::mm::DEKO_FRAME_ALLOCATOR;

verus! {

pub broadcast axiom fn axiom_array_size_wf()
    ensures
        #[trigger] Array::<u8, 35>::size_wf(),
        #[trigger] Array::<u8, 32>::size_wf(),
        #[trigger] Array::<u8, MSG_PAYLOAD_SIZE>::size_wf(),
;

/// Version of the message header
const HDR_VERSION: u8 = 1;

/// Version of the message payload
const MSG_VERSION: u8 = 1;

#[derive(Clone, Copy, DekoDebug)]
#[repr(u8)]
pub enum SnpGuestRequestAead {
    Invalid = 0,
    Aes256Gcm = 1,
}

#[derive(Clone, Copy, DekoDebug)]
#[repr(u8)]
pub enum SnpGuestRequestMsgType {
    Invalid = 0,
    ReportRequest = 5,
    ReportResponse = 6,
}

impl WellFormed for SnpGuestRequestMsgType {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

/// Message header size
const MSG_HDR_SIZE: usize = 0x60;

// size_of is exec so not supported
/// Message payload size
const MSG_PAYLOAD_SIZE: usize = (PAGE_SIZE as usize) - MSG_HDR_SIZE;

/// Maximum buffer size that the hypervisor takes to store the
/// SEV-SNP certificates
pub const SNP_GUEST_REQ_MAX_DATA_SIZE: usize = 4 * (PAGE_SIZE as usize);

/// SNP Guest Request Message Header
#[repr(C, packed)]
#[derive(Clone, Copy, DekoDebug)]
pub struct SnpGuestRequestMsgHdr {
    /// Message authentication tag
    pub authtag: Array<u8, 32>,
    /// The sequence number for this message
    pub msg_seqno: u64,
    /// Reserve. Must be zero.
    pub rsvd1: u64,
    /// The AEAD used to encrypt this message
    pub algo: u8,
    /// The version of the message header
    pub hdr_version: u8,
    /// The size of the message header in bytes
    pub hdr_sz: u16,
    /// The type of the payload
    pub msg_type: u8,
    /// The version of the payload
    pub msg_version: u8,
    /// The size of the payload in bytes
    pub msg_sz: u16,
    /// Reserved. Must be zero.
    pub rsvd2: u32,
    /// The ID of the VMPCK used to protect this message
    pub msg_vmpck: u8,
    /// Reserved. Must be zero.
    pub rsvd3: Array<u8, 35>,
}

impl WellFormed for SnpGuestRequestMsgHdr {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.authtag.wf()
    }
}

#[verus_verify]
impl SnpGuestRequestMsgHdr {
    /// Allocate a new [`SnpGuestRequestMsgHdr`] and initialize it
    #[verus_spec(r =>
        ensures
            r.wf(),
    )]
    pub fn new(msg_sz: u16, msg_type: SnpGuestRequestMsgType, msg_seqno: u64) -> Self {
        broadcast use axiom_array_size_wf;

        Self {
            msg_seqno,
            algo: SnpGuestRequestAead::Aes256Gcm as u8,
            hdr_version: HDR_VERSION,
            hdr_sz: MSG_HDR_SIZE as u16,
            msg_type: msg_type as u8,
            msg_version: MSG_VERSION,
            msg_sz,
            msg_vmpck: 0,
            authtag: Array::fill(0),
            rsvd1: 0,
            rsvd2: 0,
            rsvd3: Array::fill(0),
        }
    }
}

/// `SNP_GUEST_REQUEST` message format
#[repr(C, align(4096))]
#[derive(Clone, Copy, DekoDebug)]
pub struct SnpGuestMsg {
    pub hdr: SnpGuestRequestMsgHdr,
    pub pld: Array<u8, MSG_PAYLOAD_SIZE>,
}

impl WellFormed for SnpGuestMsg {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.hdr.wf()
        &&& self.pld.wf()
    }
}

/// Communication between an SEV guest and the SEV firmware in the AMD Secure Processor
/// (ASP, aka PSP) is protected by a VM Platform Communication Key (VMPCK). By default,
/// the sev-guest driver uses the VMPCK associated with the VM Privilege Level (VMPL) at
/// which the guest is running.
///
/// This driver implements the communication logic for the SEV SNP guest driver so that
/// we can, for example, fetch the raw report from the ASP.
///
/// See also [this](https://docs.kernel.org/virt/coco/sev-guest.html).
#[derive(DekoDebug)]
pub struct SnpGuestDriver {
    pub request: DekoPPtr<SnpGuestMsg>,
    pub response: DekoPPtr<SnpGuestMsg>,
    /// Additional buffer to store the extended data from the PSP.
    pub ext_data: DekoPPtr<Array<u8, SNP_GUEST_REQ_MAX_DATA_SIZE>>,
    /// It will be provided to the hypervisor.
    pub user_extdata_size: usize,
    /// Each `SNP_GUEST_REQUEST` message contains a sequence number per VMPCK.
    /// The sequence number is incremented with each message sent. Messages
    /// sent by the guest to the PSP and by the PSP to the guest must be
    /// delivered in order. If not, the PSP will reject subsequent messages
    /// by the guest when it detects that the sequence numbers are out of sync.
    ///
    /// Other layers in the software stack (e.g. OVMF and guest kernel) can send
    /// non-VMPL0 commands directly to PSP. Therefore, the SVSM needs to maintain
    /// the sequence number and the VMPCK only for VMPL0.
    pub vmpck0_seqno: u64,
}

with_permission! {
    SnpGuestDriver,
    request_perm: DekoPointsTo<SnpGuestMsg>,
    response_perm: DekoPointsTo<SnpGuestMsg>,
    extdata_perm: DekoPointsTo<Array<u8, SNP_GUEST_REQ_MAX_DATA_SIZE>>,
}

with_atomic_pred!(
    SnpGuestDriver,
    SnpGuestDriverPermission,
    fields: { },
    perm_fields: {},
    data.wf_with(perm)
);

#[verus_verify]
impl SnpGuestDriver {
    #[verifier::inline]
    pub open spec fn wf_with(&self, perm: SnpGuestDriverPermission) -> bool {
        &&& self.request@ == perm.request_perm.pptr()
        &&& self.response@ == perm.response_perm.pptr()
        &&& self.ext_data@ == perm.extdata_perm.pptr()
        &&& self.request.wf()
        &&& self.response.wf()
        &&& self.ext_data.wf()
    }

    /// Createsa new SNP Guest Driver instance.
    #[verus_spec(r =>
        with
            -> request_perm: Tracked<SnpGuestDriverPermission>,
        ensures
            r.wf(),
            r.wf_with(request_perm@),
    )]
    pub fn new() -> Self {
        let (request, Tracked(request_perm)) = boxed_ptr!(SnpGuestMsg, &DEKO_FRAME_ALLOCATOR.0);
        let (response, Tracked(response_perm)) = boxed_ptr!(SnpGuestMsg, &DEKO_FRAME_ALLOCATOR.0);
        let (ext_data, Tracked(extdata_perm)) =
            boxed_ptr!(Array<u8, SNP_GUEST_REQ_MAX_DATA_SIZE>, &DEKO_FRAME_ALLOCATOR.0);

        proof_with!(|= Tracked(
            SnpGuestDriverPermission {
                request_perm,
                response_perm,
                extdata_perm,
            }
        ));
        Self { request, response, ext_data, user_extdata_size: 0, vmpck0_seqno: 0 }
    }
}

impl WellFormed for SnpGuestDriver {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

pub exec static GUEST_DRIVER: DekoOnceCell<
    SnpGuestDriver,
    SnpGuestDriverPermission,
    SnpGuestDriverPred,
>
    ensures
        GUEST_DRIVER.wf(),
{
    DekoOnceCell::new(Ghost(SnpGuestDriverPred {  }))
}

/// Initialize the SNP guest driver.
#[inline]
#[verus_spec()]
pub fn init_snp_guest_driver() {
    kinfo!("Initializing SNP Guest Driver");

    proof_with!(=> Tracked(snp_driver_perm));
    let snp_driver = SnpGuestDriver::new();

    GUEST_DRIVER.init(DekoAtomicData::new_with(snp_driver, Tracked(snp_driver_perm)));
}

} // verus!
