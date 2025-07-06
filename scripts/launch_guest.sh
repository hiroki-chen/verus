#!/bin/bash
# Adapted from https://github.com/confidential-containers/td-shim/blob/main/sh_script/launch-rust-td.sh

QEMU="/usr/local/bin/qemu-system-x86_64"
BINARY="target/release/boot.img"
BIOS="/cc/tdx-linux/edk2/OVMF.fd"

# QEMU CONFIG
CORES=4
THREADS=2
SOCKETS=2
MEMORY=64G

if [ ! -f "${QEMU}" ]; then
    echo "QEMU binary not found at ${QEMU}. Please install QEMU and set the correct path."
    exit 1
fi

$QEMU \
    -enable-kvm \
    -smp cores=${CORES},threads=${THREADS},sockets=${SOCKETS} \
    -m ${MEMORY} \
    -cpu host \
    -nographic \
    -object memory-backend-ram,id=mem0,size=${MEMORY} \
    -machine q35,kernel-irqchip=split,confidential-guest-support=tdx,memory-backend=mem0 \
    -bios ${BIOS} \
    -vga none \
    -nodefaults \
    -serial stdio \
    -object iommufd,id=iommufd0 \
    -device pcie-root-port,id=pci.1,bus=pcie.0 \
    -object '{"qom-type":"tdx-guest","id":"tdx"}' \
    -drive file=${BINARY},if=virtio,format=raw
