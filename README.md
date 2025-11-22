# Deko: Attesting Runtime Isolation Policies for Secure CVMs

Deko is a formally verified reference monitor for modern Confidential Virtual Machines (CVMs) that performs *runtime attestation* on user-defined privacy policies, including access control over sensitive data and information flow control.

## Overview

Deko leverages modern hardware features for finer-grained privilege isolation inside CVMs to bypass untrusted guest kernel interference with user-level applications while preserving essential kernel functionalities. The monitor utilizes:

- **Intel TDX**: Trust Domain Extensions with TDP (Trust Domain Privilege levels)
- **AMD SEV-SNP**: Secure Encrypted Virtualization with VMPL (Virtual Machine Privilege Levels)

To ensure security-critical correctness, Deko is formally verified using [Verus](https://github.com/verus-lang/verus), a verification framework for Rust.

## Table of Contents

- [System Requirements](#system-requirements)
- [Quick Start](#quick-start)
- [Building from Source](#building-from-source)
- [Project Structure](#project-structure)
- [Documentation](#documentation)
- [Development](#development)
- [Acknowledgements](#acknowledgements)
- [License](#license)

## System Requirements

### Hardware

- **CPU**: 
  - Intel Xeon 5th Gen or later with TDX Module ≥ 1.5, OR
  - AMD EPYC 7000/9000 Series with SNP firmware ≥ 1.51
- **RAM**: Minimum 4 GB allocated for the VM

### Software

- **Host OS**: Ubuntu 24.04 (or later) with supported kernel
- **Tools**: Docker (recommended for development environment)

## Quick Start

### Prerequisites Setup

For a complete development environment setup, see **[docs/Preparation.md](docs/Preparation.md)** for detailed instructions.

**Quick setup:**
```bash
# Install system dependencies
sudo apt install -y build-essential cmake ninja-build python3 git pkg-config libssl-dev

# Clone the repository
git clone https://github.com/hiroki-chen/cage-sev.git
cd cage-sev

# Set up KVM access
sudo usermod -a -G kvm $USER && newgrp kvm

# Bootstrap development tools (takes 15-30 minutes)
cargo run --bin xtask -- bootstrap-verus
```

### Building the Monitor

```bash
# Build all components
cargo run --bin xtask -- build --target all --release

# Create bootable image
cargo run --bin xtask -- create-bootable

# Run with QEMU
cargo run --bin xtask -- qemu
```

## Building from Source

All build operations are handled through the integrated xtask build system. See the **[Build Guide](docs/Build.md)** for comprehensive instructions.

### Complete Build Process

```bash
# 1. Bootstrap required tools (one-time setup)
cargo run --bin xtask -- bootstrap-verus
cargo run --bin xtask -- bootstrap-qemu    # Optional but recommended
cargo run --bin xtask -- bootstrap-ovmf    # Optional for SVSM support

# 2. Build all components
cargo run --bin xtask -- build --target all --release

# 3. Create bootable image
cargo run --bin xtask -- create-bootable

# 4. Test with QEMU
cargo run --bin xtask -- qemu
```

The build system automatically handles:
- Cross-compilation for TDX/SNP architectures
- Formal verification with Verus
- Dependency management
- Tool integration (QEMU, OVMF, etc.)

## Project Structure

Deko is organized as a Rust workspace with multiple crates, each serving a specific purpose:

| Crate | Description |
|-------|-------------|
| **`deko-core`** | Main monitor implementation with hardware abstraction layer (HAL) |
| **`deko-std`** | Standard library for formal specifications, mathematical reasoning, and proofs |
| **`deko-stage1`** | UEFI bootloader for bootstrapping the monitor inside TDX CVMs |
| **`deko-meta`** | Boot header metadata |
| **`deko-logging`** | Serial port logger for debugging |
| **`deko-macros`** | Procedural macros for generating proofs and specifications |
| **`xtask`** | Build automation and tooling |

### Binary Crates

| Binary | Description |
|--------|-------------|
| **`bin/deko-monitor`** | Main monitor binary executable |
| **`bin/deko-stage2`** | Stage 2 bootloader for monitor initialization |

### Test Crates

| Test Crate | Description |
|------------|-------------|
| **`tests/buddy`** | Buddy allocator testing and verification |
| **`tests/elf`** | ELF loader and parsing tests |

### Hardware Abstraction

Deko supports both Intel TDX and AMD SEV-SNP through a carefully designed hardware abstraction layer located in `deko-core/src/hal.rs`. This minimizes disruption from platform-specific differences and enables portable code across architectures.

## Documentation

Detailed documentation is available in the `docs/` directory:

- **[Build.md](docs/Build.md)**: Comprehensive build instructions
- **[Debug.md](docs/Debug.md)**: Debugging guide and techniques
- **[Preparation.md](docs/Preparation.md)**: Environment setup and preparation
- **[Paging.md](docs/Paging.md)**: Memory paging implementation details
- **[address.md](docs/address.md)**: Address space management
- **[install-sev.md](docs/install-sev.md)**: SEV-specific installation guide

## Development

### Building with Cargo

Standard Rust build commands are supported:

```bash
# Development build
cargo build

# Release build
cargo build --release

# Build with Verus verification
cargo verus build
```

### Project Configuration

- **Rust toolchain**: Specified in `rust-toolchain.toml`
- **Code formatting**: Configured in `.rustfmt.toml`
- **Workspace**: Managed via `Cargo.toml` workspace definition

### Testing

```bash
$ cargo test-buddy

════════════════════ Testing buddy ════════════════════
🔨 Building test binary for 'buddy'...
Running: "cargo" "verus" "build" "--bin" "buddy"
✓ Built test binary for 'buddy'
🚀 Executing test binary: "/home/.../cage-sev/target/debug/buddy"
✓ Test suite 'buddy' PASSED

════════════════════════════════════════════════════════════
🎉 All tests PASSED (1)
```

## Acknowledgements

This project builds upon and is inspired by the following excellent projects:

- [coconut-svsm](https://github.com/coconut-svsm/svsm): AMD SEV-SNP Secure VM Service Module
- [VeriSMo](https://github.com/microsoft/verismo): Formally verified security monitor
- [linux-svsm](https://github.com/AMDESE/linux-svsm): Linux-based SVSM implementation

We extend our sincere gratitude to the authors and contributors of these projects.

## License

[Include your license information here]

## Citation

If you use Deko in your research, please cite:

```bibtex
[Include citation information here]
```

## Contact

For questions, issues, or contributions, please:
- Open an issue on GitHub
- Contact the maintainers at [contact information]

---

**Status**: Active Development | **Version**: 0.1.0 (Alpha)
