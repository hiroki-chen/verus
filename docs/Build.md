# Build Guide

This guide covers building all components of the CAGE-SEV kernel project using the integrated xtask build system.

## Table of Contents

1. [Prerequisites](#prerequisites)
2. [Build System Overview](#build-system-overview)
3. [Building Components](#building-components)
4. [Target Architectures](#target-architectures)
5. [Advanced Build Options](#advanced-build-options)
6. [Troubleshooting](#troubleshooting)

## Prerequisites

Before building, ensure you have completed the setup in **[Preparation.md](Preparation.md)**:

- ✅ System dependencies installed
- ✅ Rust toolchain configured
- ✅ KVM/SEV access set up
- ✅ Verus bootstrapped (required)
- ✅ QEMU and OVMF bootstrapped (optional but recommended)

## Build System Overview

CAGE-SEV uses a custom build system implemented in the `xtask` crate. This provides a unified interface for building all components with proper dependency management and verification.

### Build Targets

| Target | Description | Usage |
|--------|-------------|-------|
| `all` | Build all components | Full system build |
| `stage1` | UEFI bootloader | Initial boot environment |
| `deko-core` | Main monitor | Core functionality |
| `deko-std` | Standard library | Verification support |
| `deko-logging` | Logging system | Debug support |

### Build Modes

- **Development**: Fast compilation, debug symbols included
- **Release**: Optimized compilation, smaller binaries
- **Verification**: Includes formal verification with Verus

## Building Components

### Basic Build Commands

```bash
# Build all components (development mode)
cargo run --bin xtask -- build --target all

# Build with optimizations (release mode)
cargo run --bin xtask -- build --target all --release

# Build specific component
cargo run --bin xtask -- build --target stage1
cargo run --bin xtask -- build --target deko-core
```

### Verification Build

Include formal verification during build:

```bash
# Build with verification (requires Verus)
cargo run --bin xtask -- build --target all --verify

# Verification + release optimizations
cargo run --bin xtask -- build --target all --release --verify
```

### Build Output

Built artifacts are placed in target directories:

```
target/
├── x86_64-tdx-deko/           # TDX builds
│   ├── debug/
│   └── release/
├── x86_64-snp-deko/           # SNP builds
│   ├── debug/
│   └── release/
└── verus/                     # Verification artifacts
```

## Target Architectures

### Intel TDX (Default)

```bash
# Explicit TDX target
cargo run --bin xtask -- --target-arch tdx build --target all

# TDX is default, so this is equivalent:
cargo run --bin xtask -- build --target all
```

### AMD SNP

```bash
# Build for AMD SNP
cargo run --bin xtask -- --target-arch snp build --target all
```

### Cross-compilation Notes

- Each architecture produces separate binaries
- Hardware-specific code is conditionally compiled
- Verification proofs are architecture-agnostic where possible

## Advanced Build Options

### Environment Variables

Control build behavior with these environment variables:

```bash
# Custom Verus location
export VERUS_PATH=/path/to/custom/verus

# Custom Z3 location
export VERUS_Z3_PATH=/path/to/custom/z3

# Parallel build jobs
export CARGO_BUILD_JOBS=8

# Verbose output
export RUST_LOG=debug
```

### Incremental Builds

Rust's incremental compilation is enabled by default:

```bash
# Clean build (removes incremental cache)
cargo clean

# Force rebuild of specific target
cargo run --bin xtask -- build --target deko-core --clean
```

### Build Features

Enable optional features during build:

```bash
# Build with logging support
cargo run --bin xtask -- build --target all --features logging

# Build with debugging features
cargo run --bin xtask -- build --target all --features debug

# Multiple features
cargo run --bin xtask -- build --target all --features logging,debug
```

## Creating Bootable Images

After building components, create bootable images:

```bash
# Create bootable disk image
cargo run --bin xtask -- create-bootable

# Create QEMU-compatible image
cargo run --bin xtask -- create-bootable --format qemu

# Create image for specific architecture
cargo run --bin xtask -- --target-arch snp create-bootable
```

### Image Output

Bootable images are created in the `images/` directory:

```
images/
├── deko-tdx.img              # TDX bootable image
├── deko-snp.img              # SNP bootable image
└── metadata/                 # Build metadata
```

## Verification Integration

When Verus is enabled, the build process includes formal verification:

### Verification Phases

1. **Specification Check**: Verify formal specifications
2. **Proof Validation**: Check mathematical proofs
3. **Code Generation**: Generate verified code
4. **Integration**: Link verified components

### Verification Output

```bash
# Build with detailed verification output
cargo run --bin xtask -- build --target all --verify --verbose

# Verification-only (no binary generation)
cargo run --bin xtask -- verify --target all
```

## Build Performance

### Optimization Tips

- **Parallel builds**: Use `CARGO_BUILD_JOBS` to control parallelism
- **Incremental**: Avoid `cargo clean` unless necessary
- **Target selection**: Build only needed components
- **Release mode**: Use `--release` for production builds

### Build Times

Typical build times on a modern development machine:

| Target | Debug | Release | With Verification |
|--------|--------|---------|------------------|
| stage1 | 30s | 45s | 2-3 min |
| deko-core | 2-3 min | 4-5 min | 8-10 min |
| all | 5-7 min | 8-12 min | 15-20 min |

## Troubleshooting

### Common Build Issues

**Verification failures:**
```bash
# Check Verus installation
./tools/verus --version

# Rebuild verification tools
cargo run --bin xtask -- bootstrap-verus
```

**Dependency issues:**
```bash
# Update dependencies
cargo update

# Clean rebuild
cargo clean && cargo run --bin xtask -- build --target all
```

**Architecture errors:**
```bash
# Verify target architecture support
rustup target list | grep x86_64

# Check cross-compilation setup
cargo run --bin xtask -- --target-arch snp build --check
```

### Build Logs

Detailed build logs are available:

```bash
# View build logs
ls logs/build-*.log

# Follow build progress
tail -f logs/build-$(date +%Y%m%d).log
```

### Getting Help

**Environment diagnostics:**
```bash
# Check build environment
cargo run --bin xtask -- doctor

# Verify component status
cargo run --bin xtask -- status
```

**Clean rebuild procedure:**
```bash
# Complete clean rebuild
rm -rf target/ && cargo clean
cargo run --bin xtask -- bootstrap-verus
cargo run --bin xtask -- build --target all --release
```

## Integration with IDE

### VS Code

Configure VS Code for optimal development:

```json
// .vscode/settings.json
{
    "rust-analyzer.cargo.target": "x86_64-tdx-deko",
    "rust-analyzer.check.command": "clippy",
    "rust-analyzer.cargo.features": ["logging", "debug"]
}
```

### Debugging

Build with debug symbols for development:

```bash
# Development build with debug info
cargo run --bin xtask -- build --target all --debug

# Generate debug information for release builds
cargo run --bin xtask -- build --target all --release --debug-info
```

---

For more detailed usage scenarios, see:
- **[Debug.md](Debug.md)** - Debugging techniques and tools
- **[Preparation.md](Preparation.md)** - Environment setup requirements
