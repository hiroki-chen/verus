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

### Using Docker (Recommended)

Build the development Docker image:

```bash
docker build -f Dockerfile -t deko-dev . \
  --build-arg HOST_UID=$(id -u) \
  --build-arg HOST_GID=$(id -g)
```

Launch the development environment:

```bash
docker run --user "$(id -u):$(id -g)" \
  -v $(pwd):/app -it deko-dev /bin/bash
```

Inside the container, build the monitor:

```bash
cargo verus build
```

## Building from Source

### Prerequisites

To create a fully functional environment, you need to build several components with SVSM support:

1. **Linux host kernel** with SVSM support
2. **Linux guest kernel** with SVSM support  
3. **EDK2 firmware** with SVSM support
4. **QEMU emulator** with IGVM guest launching support

> **Note**: SVSM is not yet merged into the upstream kernel, so we use community-forked versions.

### Build Scripts

Run these scripts in order to set up the environment:

```bash
# Build EDK2 firmware
./scripts/edk2.sh

# Build and install QEMU (installs to ~/.local/bin)
./scripts/qemu.sh

# Build guest kernel (output: ./build/linux/arch/x86/boot/bzImage)
./scripts/guest.sh
```

### Creating the Monitor Image

Package the kernel and monitor into a TDVF file:

```bash
./scripts/stage1.sh
```

This produces `target/x86_64-tdx-deko/release/deko.bin`, which serves as the BIOS file containing the Deko monitor and the OS kernel loader.

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
| **`deko-playground`** | Testing and experimentation environment |
| **`xtask`** | Build automation and tooling |

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
# Run tests
cargo test

# Run tests in the playground
cd deko-playground && cargo test
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
