#!/bin/bash

QEMU="/home/haobchen/.local/bin/qemu-system-x86_64"
IGVM="target/x86_64-sev-deko/release/deko.igvm"

if [ ! -f "${IGVM}" ]; then
    echo "IGVM configuration file not found at ${IGVM}. Please build the IGVM configuration first."
    exit 1
fi

# QEMU CONFIG
SMP="16"
MEMORY="16G"
SEV="1"
SEV_OBJ=""
MACHINE="type=q35,igvm-cfg=igvm0,memory-backend=ram1"

if [ "${SEV}" == "1" ]; then
    MACHINE+=",confidential-guest-support=sev0"
    SEV_OBJ+="-object sev-snp-guest,id=sev0,cbitpos=51,reduced-phys-bits=1"
fi

if [ ! -f "${QEMU}" ]; then
    echo "QEMU binary not found at ${QEMU}. Please install QEMU and set the correct path."
    exit 1
fi

set -x

$QEMU -enable-kvm \
    -cpu EPYC-v4,host-phys-bits=true \
    -smp ${SMP} \
    -m ${MEMORY} \
    -machine ${MACHINE} \
    -nographic \
    -enable-kvm \
    -device virtio-scsi-pci,id=scsi0,disable-legacy=on,iommu_platform=on \
    -object memory-backend-memfd,id=ram1,size=${MEMORY},share=on,prealloc=false,reserve=false \
    -object igvm-cfg,id=igvm0,file=${IGVM} \
    ${SEV_OBJ} \
    -netdev user,id=vmnic -device e1000,netdev=vmnic,romfile= \
    -no-reboot
