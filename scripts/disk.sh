#!/bin/bash

# Stop the script if any command fails
set -e

echo "--- Building Stage-1 UEFI Loader ---"
cargo build --package deko-stage1 --target x86_64-unknown-uefi --release

echo "--- Building Deko Core ---"
cargo build --package deko-core --target .config/x86_64-tdx-deko.json --release

echo "--- Creating Boot Image ---"

# --- Configuration ---
# Define all our paths as variables for clarity
STAGE1_EFI="target/x86_64-unknown-uefi/release/deko-stage1.efi"
CORE_BIN="target/x86_64-deko-core/release/deko-core"
BOOT_IMG="target/boot.img" # Put the final image in the main target dir

# --- Image Creation ---
# Ensure the target directory exists
mkdir -p $(dirname ${BOOT_IMG})

# Create a 64MB disk image
dd if=/dev/zero of=${BOOT_IMG} bs=1M count=64

# Format it as FAT32
mkfs.fat -F 32 ${BOOT_IMG}

# Create the required directory structure
mmd -i ${BOOT_IMG} ::/EFI
mmd -i ${BOOT_IMG} ::/EFI/BOOT

# Copy the UEFI loader to the standard boot path
echo "Copying Stage-1 Loader..."
mcopy -i ${BOOT_IMG} ${STAGE1_EFI} ::/EFI/BOOT/BOOTX64.EFI

# Copy the core binary to the root of the image
echo "Copying Deko Core..."
mcopy -i ${BOOT_IMG} ${CORE_BIN} ::/deko-core.bin

echo "--- Boot Image Created Successfully at ${BOOT_IMG} ---"
