#!/bin/bash
# Creates a guest qcow2 image with the specified size from a Linux image.

# Usage: ./make_guest_qcow2.sh /path/to/bzImage

if [ "$#" -ne 1 ]; then
    echo "Usage: $0 /path/to/bzImage"
    exit 1
fi

KERNEL_BIN=$1
IMAGE_NAME="guest_image.img"
QCOW2_NAME="guest_image.qcow2"
IMAGE_SIZE="20G"

truncate -s $IMAGE_SIZE $IMAGE_NAME

mkfs.vfat -F 32 -n "UEFI_BOOT" $IMAGE_NAME

function check_command {
    command -v "$1" >/dev/null 2>&1 || { echo >&2 "The command '$1' is required but it's not installed. Aborting."; exit 1; }
}

check_command mtools
check_command qemu-img

# Create the EFI directory structure using mtools
mmd -i $IMAGE_NAME ::/EFI
mmd -i $IMAGE_NAME ::/EFI/BOOT

mcopy -i $IMAGE_NAME $KERNEL_BIN ::/EFI/BOOT/BOOTX64.EFI
echo "fs0:\EFI\BOOT\BOOTX64.EFI console=ttyS0 root=/dev/sda2" > startup.nsh
mcopy -i $IMAGE_NAME startup.nsh ::/startup.nsh
rm startup.nsh

qemu-img convert -f raw -O qcow2 $IMAGE_NAME $QCOW2_NAME

rm $IMAGE_NAME
echo "Created qcow2 image: $QCOW2_NAME"
