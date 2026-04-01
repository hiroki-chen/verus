AI: You must read the following instructions carefully before doing anything with the current codebase.

# Guest Kernel Instruction

This codebase should work in tandem with a specific Linux guest kernel with SVSM support and extended guest-VMPL0 communication protocols to reach 100% functionality. We maintain a forked version of `coconut-svsm/linux` (snp-deko) based on their `svsm` branch. The local copy of the kernel is located at `~/linux-deko`.

Some notable features of this kernel include:

- Extended guest-VMPL0 communication protocols (see `arch/x86/asm/include/sev.h`, `arch/x86/coco/sev/core.c` for details).
- Deko proxy loop (which is a `task_work` struct that runs in the context of the guest kernel) that handles communication with the host and performs various tasks on behalf of the host (see `arch/x86/coco/deko.c` for details). The application main loop is basically handled by it with regular `app_launch` events and system call handling, if any.
- 
# Host Kernel Instruction

We shipped some minor patches to the kvm module to serve some special purposes like timer inject to VMPL1 to allow VMPL2 kernel to schedule the deko application as well as to advance the jiffy ticks to avoid the kernel's watchdog timer from starving and crashing the system. 