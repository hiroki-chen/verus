# Deko Documentation Index

This folder contains setup, build, debug, and architecture notes for `cage-sev`.

## Getting Started

1. [Preparation Guide](Preparation.md)
2. [Build Guide](Build.md)
3. [Debug Guide](Debug.md)

## Core Docs

- [Preparation.md](Preparation.md): host setup, bootstrap, and first run
- [Build.md](Build.md): current `xtask` command reference
- [Debug.md](Debug.md): debugging and logging primitives
- [GuestTests.md](GuestTests.md): local SNP QEMU config and guest test workflow
- [logging-usage.md](logging-usage.md): ergonomic logging macros and patterns
- [install-sev.md](install-sev.md): AMD SEV-SNP host-side compatibility notes

## Architecture Notes

- [Paging.md](Paging.md)
- [address.md](address.md)
- [mem-layout.png](mem-layout.png)

## Quick Commands

```bash
# Bootstrap verifier tools
cargo run --bin xtask -- bootstrap-verus

# Build SNP artifacts
cargo run --bin xtask -- --target-arch snp build --target all --release

# Run SNP with local config
cargo qemu-snp
```

## Maintenance Notes

- Keep command examples in sync with `xtask/src/main.rs`
- Prefer explicit `--target-arch` in all monitor/QEMU examples
- Update this index whenever adding/removing docs

---

Last updated: 2026-03-09
