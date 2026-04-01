# Deko: Attesting Runtime Isolation Policies for Secure CVMs

Deko is a formally verified reference monitor for modern confidential VMs (CVMs). It enforces runtime policies (access control + information-flow constraints) even in the presence of an untrusted guest kernel.

## Overview

Deko supports both major x86 confidential-computing models:

- Intel TDX
- AMD SEV-SNP

Security-critical logic is verified with [Verus](https://github.com/verus-lang/verus).

## Quick Start

### 1. Setup

See [docs/Preparation.md](docs/Preparation.md).

```bash
git clone https://github.com/hiroki-chen/cage-sev.git
cd cage-sev
cargo run --bin xtask -- bootstrap-verus
```

### 2. Build (SNP example)

```bash
cargo run --bin xtask -- --target-arch snp build --target all --release
```

### 3. Create bootable artifact + run QEMU

```bash
cargo run --bin xtask -- --target-arch snp create-bootable
cargo run --bin xtask -- --target-arch snp qemu --config-path .config/qemu.snp.config.toml
```

For TDX, replace `snp` with `tdx` and use `.config/qemu.tdx.config.toml`.

## Build System

All primary workflows are in `xtask`:

- `build`
- `create-bootable`
- `qemu`
- `stress-test`
- `test`
- `bootstrap-verus`
- `bootstrap-qemu`
- `bootstrap-ovmf`

Detailed command reference: [docs/Build.md](docs/Build.md)

Common alias-based entry points:

```bash
cargo build-deko-snp-debug
cargo qemu-snp
cargo qemu-snp-stress -- --iter 10 --timeout 30
```

## Project Structure

| Path | Description |
|---|---|
| `deko-core` | Core monitor implementation |
| `deko-std` | Shared spec/proof utilities |
| `deko-stage1` | UEFI stage1 bootloader |
| `deko-logging` | Logging primitives/macros support |
| `bin/deko-stage2` | Stage2 bootloader binary crate |
| `bin/deko-monitor` | Main monitor binary crate |
| `xtask` | Build/bootstrap/run tooling |

## Documentation

- [docs/README.md](docs/README.md)
- [docs/Preparation.md](docs/Preparation.md)
- [docs/Build.md](docs/Build.md)
- [docs/Debug.md](docs/Debug.md)
- [docs/logging-usage.md](docs/logging-usage.md)

## Development Notes

- Rust toolchain is pinned in `rust-toolchain.toml`
- Cargo aliases are defined in `.cargo/config.toml`
- Most workflows require explicit `--target-arch`

## Status

Active development.
