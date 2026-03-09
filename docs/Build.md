# Build Guide

This guide documents the actual `xtask` commands currently implemented in this repository.

## Prerequisites

Complete setup first:

- [Preparation.md](Preparation.md)
- `cargo run --bin xtask -- bootstrap-verus` (required)
- `cargo run --bin xtask -- bootstrap-qemu` (optional)
- `cargo run --bin xtask -- bootstrap-ovmf` (optional)

## Key Rule: Always Set Architecture

`xtask` supports `--target-arch {tdx|snp|init}` as a global option.

Use `--target-arch` explicitly for monitor builds and QEMU runs:

```bash
cargo run --bin xtask -- --target-arch snp build --target all --release
cargo run --bin xtask -- --target-arch tdx build --target all --release
```

## Build Targets

`build --target` currently supports:

- `all`
- `deko`
- `stage1`
- `init`

Examples:

```bash
# SNP full build
cargo run --bin xtask -- --target-arch snp build --target all --release

# TDX full build
cargo run --bin xtask -- --target-arch tdx build --target all --release

# Build only stage1
cargo run --bin xtask -- --target-arch tdx build --target stage1 --release

# Build only init
cargo run --bin xtask -- --target-arch init build --target init --release
```

## Create Bootable Artifacts

```bash
# SNP: create IGVM image
cargo run --bin xtask -- --target-arch snp create-bootable

# TDX: create FAT boot image
cargo run --bin xtask -- --target-arch tdx create-bootable
```

Notes:

- SNP output is generated under `target/x86_64-snp-deko/debug/igvm.igvm` by default.
- TDX output is generated under `target/x86_64-tdx-deko/debug/boot.img` by default.

## Run QEMU

Use arch-specific config files:

```bash
# SNP
cargo run --bin xtask -- --target-arch snp qemu --config-path .config/qemu.snp.config.toml

# TDX
cargo run --bin xtask -- --target-arch tdx qemu --config-path .config/qemu.tdx.config.toml
```

Or use Cargo aliases from `.cargo/config.toml`:

```bash
cargo qemu-snp
cargo qemu-tdx
```

## Bootstrap Commands

```bash
# Verus + Z3
cargo run --bin xtask -- bootstrap-verus

# QEMU (IGVM-enabled fork)
cargo run --bin xtask -- bootstrap-qemu

# OVMF
cargo run --bin xtask -- bootstrap-ovmf
```

## Test and Utility Commands

```bash
# Run all test suites under tests/
cargo run --bin xtask -- test

# Run one suite, e.g. buddy
cargo run --bin xtask -- test buddy

# Pretty-print / formatting helper
cargo run --bin xtask -- pretty --paths deko-core/src

# Verification line counting helper
cargo run --bin xtask -- line-count

# Repeated QEMU boot test
cargo run --bin xtask -- --target-arch snp stress-test --iter 10 --timeout 30 --config-path .config/qemu.snp.config.toml
```

## Environment Variables

- `VERUS_PATH`: custom path to `verus`
- `VERUS_Z3_PATH`: custom path to `z3`
- `QEMU_BIN`: custom path to `qemu-system-x86_64`

## Removed Old/Invalid Examples

The following examples were removed because they are not supported by current `xtask` CLI:

- `build --verify`
- `build --clean`
- `build --features ...`
- `create-bootable --format qemu`
- `verify --target ...`
- `doctor`
- `status`
- `build --debug` / `--debug-info`

If these flags are needed again, they should be added to `xtask/src/main.rs` first.
