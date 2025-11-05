//! Platform implementation abstraction layer
//!
//! This module provides a unified interface for platform-specific operations,
//! allowing the core code to be platform-agnostic while selecting the appropriate
//! implementation at compile time through feature flags.
// Re-export the appropriate platform implementation based on feature flags
#[cfg(feature = "snp")]
pub use crate::snp::*;
#[cfg(feature = "tdx")]
pub use crate::tdx::*;

// Ensure exactly one platform feature is enabled
#[cfg(not(any(feature = "snp", feature = "tdx")))]
compile_error!("Must enable either 'snp' or 'tdx' feature");

#[cfg(all(feature = "snp", feature = "tdx"))]
compile_error!("Cannot enable both 'snp' and 'tdx' features");
