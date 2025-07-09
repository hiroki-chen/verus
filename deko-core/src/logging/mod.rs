//! Debug logging feature for the monitor; enable only for debugging purposes only. You should disable this for safety reasons.
//!
//! This crate currently DOES NOT use the `vstd` crate to verify its implementation as it is designed solely for debugging.
#[cfg(feature = "logging")]
pub mod imp {
    use deko_logging::*;
}

#[cfg(not(feature = "logging"))]
pub mod imp {}

pub use imp::*;
