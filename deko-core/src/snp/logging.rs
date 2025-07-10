//! This debugging tool implements logging functionality for SNP guests.
//!
//! Since SNP does not allow direct print to console,
//! we will need to leverage the GHCB protocol for this purpose.
//!
//! Also notice that SNP has very poor support for debugging using gdb so it'd better
//! to use logging. Also notice that logging is extremely dangerous as this could
//! interfere with information flow control. So it should only be enabled on debug.
