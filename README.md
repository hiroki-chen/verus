# Deko: Attesting Runtime Isolation Policies for Secure CVMs.

Deko is a reference monitor for modern Confidential VMs (e.g., Intel TDX, AMD SEV-SNP) to perform *runtime attesation* on user-defined privacy policies (access control over sensitive data, information flow control, etc.). It utilizes modern hardware features that support finer-grained privilege isolation inside the CVM to bypass the untrusted guest kernel's interference with user-level applications while preserving its functionalities. We utilize TDP for TDX and VMPL for SNP to implement Deko as a privileged monitor. Furthermore, since this monitor is security-critical, we use Verus to formally verify the correctness properties.

## System Requirements

We expect the developers to have SNP or TDX-supported hardware available to build and play with Deko.

- CPU: Intel Xeon 5th Gen or Later with TDX Module >= 1.5 / AMD EPYC 7000/9000 Series with SNP firmware >= 1.51
- RAM: At least 4 GB allocated for the VM.
- Host OS: Ubuntu 24.04 with supported kernel (see below to build the required kernel).

## Build

We have provided you with a Dockerfile to build the image and play with the code. To build the image, run:

```bash
docker build -f Dockerfile -t deko-dev . --build-arg HOST_UID=`id -u` --build-arg HOST_GID=`id -g`
```

Then you should be able to have the verus environment and launch the docker environment with the current directory mounted:

```bash
$ docker run --user "$(id -u):$(id -g)" -v $(pwd):/app -it deko-dev /bin/bash
root@4187ae31e1c8:/app#
```

Build the monitor is super easy:

```bash
root@4187ae31e1c8:/app# cargo verus build
```

### Preparing the guest

In order to create a working Linux guest image, security monitor for SEV-SNP, and the QEMU emulator for running the guest, you would need to run the following scripts to do the magic under the hood. Note that since SVSM is still not merged into the upstream kernel we will need to build the community forked version:

- Linux host kernel with SVSM support
- Linux guest kernel with SVSM support
- EDK2 with SVSM support
- A modified QEMU which supports launching guests configured using IGVM

```sh
./scripts/edk2.sh
./scripts/qemu.sh
./scripts/guest.sh
```

which will build and install an SVSM-supported QEMU under `~/.local/bin` and a minimal Linux kernel under `./build/linux/arch/x86/boot/bzImage`.

Afterwards you need to pack the kernel and the monitor image into a TDVF file for the QEMU to prepare for the guest state.

```sh
./scripts/stage1.sh
```
which will produce `target/x86_64-tdx-deko/release/deko.bin` as the BIOS file which contains the deko-monitor and the loader for the user-level OS kernel.


## Project Layout

We aim to support both TDX and SNP so we carefully designed the hardware abstraction layer to minimize the disrupt caused by platform differences. The purpose of each crate is listed below.

- `deko-core`: main implementation of the deko monitor. We hide hardware implementation details using `deko-core/src/hal.rs`.
- `deko-logging`: a serial port logger for debugging only.
- `deko-macros`: a collection of procedural macros for generating proofs and specs quickly.
- `deko-meta`: boot header.
- `deko-monitor`: stage 2 bootloader for setting up the initial context for deko entry function.
- `deko-std`: the toolbox for formal specs, mathematical reasonings, etc.
- `deko-stage`: the UEFI bootloader for bootstrapping deko monitor inside TDX CVMs.

# Acknowledgement

This project is based on the following projects:

- coconut-svsm
- VeriSMo
- linux-svsm

The authors would like to extend their sincere gratitude to the authors of the above projects.
