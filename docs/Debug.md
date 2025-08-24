# Debugging Support

Please be aware that GDB debugging is not supported in the monitor as we currently do not provide a full-stack implementation of the GDB connection protocol. While we intend to support this feature, this would require non-trivial efforts. We currently only use (non-verified) `print` to debug the guest, and we advise that this feature be disabled for production environment. For SEV-SNP guest, we utilize the Guest-Host Communication Block protocol for printing and for TDX guest, we use serial port (COM0/1) for this purpose.

Some other projects have utilized [gdbstub](https://crates.io/crates/gdbstub) to implement the GDB remote serial protocol for debugging purposes.