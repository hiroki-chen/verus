# Preparation Guide

This guide covers the minimum setup required to build and run Deko with the current `xtask` workflow.

## System Requirements

### Hardware
- CPU with either Intel TDX support or AMD SEV-SNP support
- At least 8GB RAM (16GB+ recommended)
- 20GB+ free disk space

### Software
- Linux host (Ubuntu 24.04+ recommended)
- Rust toolchain via `rustup`
- `build-essential`, `cmake`, `ninja-build`, `git`, `pkg-config`, `libssl-dev`
- Python 3

Install dependencies on Ubuntu/Debian:

```bash
sudo apt update
sudo apt install -y \
    build-essential \
    cmake \
    ninja-build \
    python3 \
    python3-pip \
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

### 1. Clone repo

```bash
git clone https://github.com/hiroki-chen/cage-sev.git
cd cage-sev
```

### 2. Rust toolchain

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source ~/.cargo/env
cargo --version
```

### 3. KVM / SEV permissions

```bash
sudo usermod -a -G kvm $USER
newgrp kvm
ls -l /dev/kvm
```

For SEV-SNP hosts, also ensure `/dev/sev` is accessible to your user/group.

## Bootstrap Required Tools

### Verus (required)

```bash
cargo run --bin xtask -- bootstrap-verus
```

### QEMU (optional)

```bash
cargo run --bin xtask -- bootstrap-qemu
```

### OVMF (optional)

```bash
cargo run --bin xtask -- bootstrap-ovmf
```

## Architecture Selection (Important)

`xtask` does not implicitly choose `tdx`/`snp` for monitor workflows. Pass `--target-arch` explicitly:

```bash
# SNP build
cargo run --bin xtask -- --target-arch snp build --target all --release

# TDX build
cargo run --bin xtask -- --target-arch tdx build --target all --release
```

## Verification Checklist

```bash
# Verus
./tools/verus --version

# Z3
./tools/z3 --version

# Optional QEMU
./tools/bin/qemu-system-x86_64 --version
```

## First End-to-End Run

```bash
# Build (SNP example)
cargo run --bin xtask -- --target-arch snp build --target all --release

# Create bootable artifact
cargo run --bin xtask -- --target-arch snp create-bootable

# Run QEMU
cargo run --bin xtask -- --target-arch snp qemu --config-path .config/qemu.snp.config.toml
```

## Environment Variables

```bash
export VERUS_PATH=/path/to/verus
export VERUS_Z3_PATH=/path/to/z3
export QEMU_BIN=/path/to/qemu-system-x86_64
```

## Troubleshooting

- Build fails early:
  - Re-run `cargo run --bin xtask -- bootstrap-verus`
- QEMU command missing:
  - Set `QEMU_BIN` or run `bootstrap-qemu`
- Permission issue with KVM/SEV:
  - Re-check group membership and device permissions

## Next Docs

- [Build.md](Build.md)
- [Debug.md](Debug.md)
- [logging-usage.md](logging-usage.md)
