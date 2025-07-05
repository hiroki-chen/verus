# TDVF

For full details please refer to Intel's doc. The information below is modified to tailor to deko's needs.

To boot into the entrypoint of the `deko-monitor` we will need to implement the TDX Virtual Firmware (TDVF) that has the following features

- Use Unified Extensible Firmware Interface (UEFI) Secure Boot as base with extensions for TD launch.
- Use Trusted Computing Group (TCG) Trusted Boot to perform a measured and verified launch of a guest OS loader or kernel.
- Simplify firmware by removing features found in traditional UEFI implementations.

A TD launch takes below steps:

- VMM sets up TDVF, calls Intel TDX module to create the initial measurement, then calls Intel TDX module to launch TDVF.
- TDVF boots and enables UEFI Secure Boot.
  - TDVF's entry must be in 32-bit protected mode and this is launched by the TDX module.
  - TDBF enables long mode.
  - TDVF parses system information passed by the hypervisor.
  - TDBF halts AP until AP wakes up.
- TDVF prepares CC event log and launches the deko entry function `_start`.

TDVF is launched on all processors and start in 32bit protected mode with flat descriptors w/o paging enabled.
