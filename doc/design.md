# Deko Design

`deko` (TDX-version) is a lightweight secure monitor for Intel TDX. It is the initial code in a Trust Domain (TD) - the TDX confidential computing environment. By design, a hypervisor (such as KVM, cloud-hypervisor, etc) launches `deko`, as the initial guest component for a Trust Domain (TD).

`deko` owns the reset vector at `0xFFFFFFF0` which performs the below actions:

- Initialize the guest TD according to TDX requirement, such as rendez-vous all application processors (AP), switch from 32bit protected mode to 64bit long mode, accept the TD private memory, and extend untrusted VMM input to the TDX Runtime Measurement Register (RTMR) with TD event log for TDX attestation.
- Enable required defenses and register all needed services for kernel isolation.
- Provide required information for the next stage payload such as memory maps and ACPI tables.
- Launch the payload: could be either a commodify kernel, a baremetal code, or everything that should be run inside the CVM.

## Entry

We define the entrypoint of the monotor inside the `deko-stage1` crate which is a `_start` function. It will initialize the monitor and the payload for later uses. The reset vector is the reset vector inside the monitor which owns the very first instruction in the TD at address 0XFFFFFFF0. This is implementedi n the IA32 code named `reset_vector`. The code switches to long mode and parkes APs, initializes the stack and does all the init stuff there.

The boot phase: VMM -> TDX Module -> ResetVector -> deko-monitor -> kernel bootloader -> kernel
