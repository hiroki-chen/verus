//! This debugging tool implements logging functionality for SNP guests.
//!
//! Since SNP does not allow direct print to console,
//! we will need to leverage the GHCB protocol for this purpose.
//!
//! Also notice that SNP has very poor support for debugging using gdb so it'd better
//! to use logging. Also notice that logging is extremely dangerous as this could
//! interfere with information flow control. So it should only be enabled on debug.
use vstd::prelude::*;
verus! {

/// A struct that implements the GHCB protocol for logging.
#[verifier::external]
#[cfg(feature = "logging")]
pub struct GHCBIo;

#[cfg(feature = "logging")]
pub fn init_logger() {
}

#[verifier::external]
#[allow(unused)]
#[cfg(feature = "logging")]
impl GHCBIo {
    pub fn outb(&self, port: u16, value: u8) {
        // This function should send the byte to the GHCB protocol.
        // The actual implementation is not provided here as it depends on the
        // specific GHCB protocol implementation.
        // For example, it could use a specific instruction to write to the port.
    }

    pub fn outw(&self, port: u16, value: u16) {
        // This function should send the word to the GHCB protocol.
        // The actual implementation is not provided here as it depends on the
        // specific GHCB protocol implementation.
        // For example, it could use a specific instruction to write to the port.
    }
}

} // verus!
