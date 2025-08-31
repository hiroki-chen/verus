//! This debugging tool implements logging functionality for SNP guests.
//!
//! Since SNP does not allow direct print to console,
//! we will need to leverage the GHCB protocol for this purpose.
//!
//! Also notice that SNP has very poor support for debugging using gdb so it'd better
//! to use logging. Also notice that logging is extremely dangerous as this could
//! interfere with information flow control. So it should only be enabled on debug.
use vstd::prelude::*;

use crate::snp::Snp;

#[cfg(feature = "logging")]
verus! {

use deko_std::prelude::*;

pub exec static GHCB_IO_PORT: OnceCellNoPred<GHCBIoPort>
    ensures
        GHCB_IO_PORT.wf(),
{
    OnceCellNoPred::new(Ghost(()))
}

/// A struct to represent the GHCB I/O port.
///
/// # Note
///
/// This struct does not lock the I/O port and it is not intended
/// to be use directly. We must wrap it through a struct, e.g.,
/// `Terminal` or `Console` that finally re-routes all the request
/// to this struct.
///
/// Furthermore, since Verus does not yet support trait objects,
/// we can only use the concrete types directly via a dispatcher.
#[derive(Clone, Copy)]
pub struct GHCBIoPort(u16);

impl WellFormed for GHCBIoPort {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl GHCBIoPort {
    pub fn new(port: u16) -> (r: Self)
        ensures
            r.wf(),
    {
        GHCBIoPort(port)
    }

    #[inline(always)]
    pub fn outb(&self, value: u8)
        requires
            self.wf(),
    {
    }

    pub fn inb(&self) {
        vstd::vpanic!("Not implemented");
    }
}

impl Snp {
    /// Initialize the GHCB logging mechanism.
    pub(crate) fn init_ghcb_logging(serial_port: u16) {
        GHCB_IO_PORT.init(GHCBIoPort::new(serial_port));
    }
}

} // verus!
#[cfg(not(feature = "logging"))]
verus! {


} // verus!
