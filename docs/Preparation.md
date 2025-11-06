# Preparation Guide

This guide walks you through setting up all necessary components to build and run the CAGE-SEV kernel project.

## Table of Contents

1. [System Requirements](#system-requirements)
2. [Initial Setup](#initial-setup)
3. [Bootstrap Components](#bootstrap-components)
4. [Verification](#verification)
5. [Troubleshooting](#troubleshooting)

## System Requirements

### Hardware Requirements
- **CPU**: Intel processor with TDX support OR AMD processor with SNP support
- **Memory**: At least 8GB RAM (16GB+ recommended)
- **Storage**: 20GB+ free disk space

### Software Requirements
- **OS**: Linux (Ubuntu 24.04+ or equivalent)
- **Rust**: Latest nightly toolchain (managed automatically)
- **Build Tools**: GCC, Make, CMake, Ninja, Git
- **Python**: Python 3.8+

### Install System Dependencies

```bash
# Ubuntu/Debian
sudo apt update
sudo apt install -y \
    build-essential \
    cmake \
    ninja-build \
    python3 \
    python3-pip \
    python3-venv \
    git \
    pkg-config \
    libssl-dev \
    libglib2-dev \
    curl \
    nasm \
    iasl \
    meson

```

## Initial Setup

### 1. Clone the Repository

```bash
git clone https://github.com/hiroki-chen/cage-sev.git
cd cage-sev
```

### 2. Install Rust Toolchain

The project uses a specific nightly Rust version defined in `rust-toolchain.toml`:

```bash
# Install rustup if not already installed
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source ~/.cargo/env

# The correct toolchain will be installed automatically when you run cargo
cargo --version
```

### 3. Set Up KVM and SEV Access

To run QEMU without sudo privileges:

```bash
# Add your user to the kvm group
sudo usermod -a -G kvm $USER

# Set up SEV device to use kvm group (for AMD SNP)
sudo chgrp kvm /dev/sev
sudo chmod 660 /dev/sev

# Create udev rule for persistent SEV device permissions
sudo tee /etc/udev/rules.d/99-sev.rules << 'EOF'
# SEV device permissions - use kvm group
KERNEL=="sev", GROUP="kvm", MODE="0660"
EOF

# Reload udev rules
sudo udevadm control --reload-rules

# Log out and log back in, or start a new session
newgrp kvm

# Verify access to both devices
ls -l /dev/kvm /dev/sev
# Should show both devices with kvm group:
# crw-rw---- 1 root kvm 10, 232 [date] /dev/kvm
# crw-rw---- 1 root kvm 10, 262 [date] /dev/sev
```

## Bootstrap Components

The project requires several specialized tools. Use the built-in bootstrap commands to set them up:

### 1. Bootstrap Verus (Required)

Verus is used for formal verification. This step builds the Verus verifier and Z3 theorem prover:

```bash
cargo run --bin xtask -- bootstrap-verus
```

**What this does:**
- Downloads and builds Verus from source
- Downloads and configures Z3 theorem prover
- Installs binaries to `tools/` directory
- Synchronizes with project's Rust toolchain

**Time required:** 15-30 minutes depending on your system

### 2. Bootstrap QEMU (Optional but Recommended)

Builds QEMU with IGVM (Isolated Guest Virtual Machine) support:

```bash
cargo run --bin xtask -- bootstrap-qemu
```

**What this does:**
- Installs cargo-c for C library building
- Downloads Microsoft IGVM library and builds it
- Downloads COCONUT-SVSM QEMU fork with IGVM support
- Builds and installs QEMU to `tools/bin/`

**Time required:** 30-60 minutes depending on your system

### 3. Bootstrap OVMF (Optional)

Builds OVMF firmware with COCONUT-SVSM support:

```bash
cargo run --bin xtask -- bootstrap-ovmf
```

**What this does:**
- Downloads COCONUT-SVSM EDK2 fork
- Builds BaseTools and OVMF firmware
- Includes TPM2 support and debug features
- Installs OVMF.fd to `tools/share/`

**Time required:** 20-40 minutes depending on your system

## Build Order and Dependencies

For a complete setup, run the bootstrap commands in this order:

```bash
# 1. Always required - builds verification tools
cargo run --bin xtask -- bootstrap-verus

# 2. For running with enhanced QEMU (recommended for SNP)
cargo run --bin xtask -- bootstrap-qemu

# 3. For custom OVMF firmware (recommended for SNP/SVSM)
cargo run --bin xtask -- bootstrap-ovmf
```

### Target Architecture Selection

The project supports two target architectures:

- **TDX (Intel)**: `cargo run --bin xtask -- --target-arch tdx <command>`
- **SNP (AMD)**: `cargo run --bin xtask -- --target-arch snp <command>`

If not specified, TDX is used by default.

## Verification

### 1. Verify Tool Installation

Check that all tools are properly installed:

```bash
# Check Verus
./tools/verus --version

# Check Z3
./tools/z3 --version

# Check QEMU (if bootstrapped)
./tools/bin/qemu-system-x86_64 --version

# Check OVMF (if bootstrapped)
ls -la tools/share/OVMF.fd
```

### 2. Build Test

Try building a component to verify everything works:

```bash
# Build stage1 bootloader
cargo run --bin xtask -- build --target stage1

# Build all components
cargo run --bin xtask -- build --target all --release
```

### 3. QEMU Test

Test QEMU functionality:

```bash
# Create a basic configuration and test QEMU
cargo run --bin xtask -- qemu --help
```

## Environment Variables

You can set these environment variables to customize tool locations:

```bash
# Custom Verus location
export VERUS_PATH=/path/to/verus

# Custom Z3 location  
export VERUS_Z3_PATH=/path/to/z3

# Custom QEMU location
export QEMU_BIN=/path/to/qemu-system-x86_64
```

## Directory Structure After Bootstrap

After successful bootstrap, your `tools/` directory should look like:

```
tools/
├── bin/
│   └── qemu-system-x86_64          # Custom QEMU (if bootstrapped)
├── lib/
│   └── x86_64-linux-gnu/
│       └── libigvm.so.0.4          # IGVM library (if QEMU bootstrapped)
├── share/
│   └── OVMF.fd                     # Custom OVMF (if bootstrapped)
├── verus                           # Verus verifier
├── z3                              # Z3 theorem prover
└── verus-root                      # Verus marker file
```

## Troubleshooting

### Common Issues

**Build failures:**
- Ensure all system dependencies are installed
- Check that you have sufficient disk space (20GB+)
- Verify internet connectivity for downloads

**Permission errors:**
- Make sure you're in the kvm group: `groups $USER | grep kvm`
- Log out and back in after adding to kvm group

**Library not found errors:**
- `LD_LIBRARY_PATH` is automatically set by the xtask tool
- If using custom tools, ensure library paths are correct

**Verification failures:**
- Ensure Verus and Z3 are properly installed
- Check that the correct nightly Rust version is active

### Getting Help

**Check logs:** All bootstrap operations create detailed logs in the `logs/` directory.

**Environment details:** Run this to check your setup:
```bash
# Check Rust version
rustc --version

# Check available tools  
ls -la tools/

# Check KVM access
ls -l /dev/kvm
```

**Clean rebuild:** If you encounter persistent issues:
```bash
# Remove tools directory and rebuild
rm -rf tools/
cargo run --bin xtask -- bootstrap-verus
# ... repeat other bootstrap commands
```

## Next Steps

After completing this preparation:

1. **Build the kernel:** Use `cargo run --bin xtask -- build --target all`
2. **Create bootable images:** Use `cargo run --bin xtask -- create-bootable`  
3. **Run with QEMU:** Use `cargo run --bin xtask -- qemu`

For more detailed usage instructions, see the main project documentation.

## Performance Notes

- **Parallel builds:** Bootstrap operations will use multiple CPU cores automatically
- **Disk space:** Keep at least 5GB free after bootstrap for builds and logs
- **Memory usage:** Some bootstrap operations are memory-intensive; close other applications if needed
- **Build caching:** Subsequent builds will be much faster due to Rust's incremental compilation

---

*This preparation typically takes 1-2 hours for a complete setup, but only needs to be done once per development environment.*
