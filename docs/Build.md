# Build Guide

This guide documents the `xtask` workflows implemented in this repository and the preferred Cargo aliases that wrap them.

## Prerequisites

Complete setup first:

- [Preparation.md](Preparation.md)
- `cargo run --bin xtask -- bootstrap-verus` (required)
- `cargo run --bin xtask -- bootstrap-qemu` (optional)
- `cargo run --bin xtask -- bootstrap-ovmf` (optional)

## xtask Overview

`xtask` is the repository task runner for build, bootstrap, QEMU launch, formatting, and test workflows.

You can invoke it in two ways:

```bash
# Direct form
cargo run --package xtask --release -- --target-arch snp qemu --config-path .config/qemu.snp.toml

# Preferred alias form when an alias exists
cargo qemu-snp
```

The aliases live in `.cargo/config.toml`. Prefer them over reconstructing the command manually when they already match the workflow you want.

## Key Rule: Always Set Architecture

`xtask` supports `--target-arch {tdx|snp|init}` as a global option.

Use `--target-arch` explicitly for monitor builds and QEMU runs:

```bash
cargo run --package xtask --release -- --target-arch snp build --target all --release
cargo run --package xtask --release -- --target-arch tdx build --target all --release
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
cargo build-deko-snp-release

# TDX full build
cargo build-deko-tdx-release

# Build only stage1
cargo run --package xtask --release -- --target-arch tdx build --target stage1 --release

# Build only init
cargo build-init-release
```

## Create Bootable Artifacts

```bash
# SNP: create IGVM image
cargo create-bootable-snp-debug

# TDX: create FAT boot image
cargo run --package xtask --release -- --target-arch tdx create-bootable
```

Notes:

- SNP output is generated under `target/x86_64-snp-deko/debug/igvm.igvm` by default.
- TDX output is generated under `target/x86_64-tdx-deko/debug/boot.img` by default.

## Run QEMU

Use arch-specific config files:

```bash
# SNP
cargo qemu-snp

# TDX
cargo qemu-tdx
```

Equivalent direct commands:

```bash
cargo run --package xtask --release -- --target-arch snp qemu --config-path .config/qemu.snp.toml
cargo run --package xtask --release -- --target-arch tdx qemu --config-path .config/qemu.tdx.config.toml
```

## Bootstrap Commands

```bash
# Verus + Z3
cargo run --package xtask --release -- bootstrap-verus

# QEMU (IGVM-enabled fork)
cargo run --package xtask --release -- bootstrap-qemu

# OVMF
cargo run --package xtask --release -- bootstrap-ovmf
```

## Test and Utility Commands

```bash
# Run all test suites under tests/
cargo run --package xtask --release -- test

# Run one suite, e.g. buddy
cargo xtest buddy

# Pretty-print / formatting helper
cargo pretty --paths xtask/src/builder.rs

# Verification line counting helper
cargo stats

# Repeated QEMU boot test
cargo qemu-snp-stress -- --iter 10 --timeout 30
```

Notes for `stress-test`:

- `--iter` is the number of QEMU launch attempts.
- `--timeout` is the per-run deadline in seconds.
- The current SNP stress-test alias uses `.config/qemu.snp.toml`.
- When passing extra arguments to a Cargo alias, include `--` before the xtask flags.

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
