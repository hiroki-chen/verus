# Deko: Formally Verified SM-Based Intra-VM Compartmentalization for CVMs

## Build

We have provided you with a Dockerfile to build the image and play with the code. To build the image, run:

```bash
docker build -t deko-dev .
```

Then you should be able to have the verus environment and launch the docker environment with the current directory mounted:

```bash
$ docker run -v $(pwd):/app -it deko-dev /bin/bash
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

Afterwards you need to pack the kernel and the monitor image into an IGVM file for the QEMU to prepare for the guest state.
