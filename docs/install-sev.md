# AMD SEV-SNP Host Notes

This document is a supplement for AMD SEV-SNP hosts.

For the general project setup and build flow, start with:

- [Preparation.md](Preparation.md)
- [Build.md](Build.md)

## Scope

Use this page when:

- You can build the project, but SNP VM launch fails on host capability checks.
- You need to validate host kernel/firmware support for SEV-SNP.

## Verify Host Capability

Check host boot logs:

```bash
sudo dmesg | egrep "SEV|RMP|ccp|kvm_amd"
```

Expected signals include:

- RMP table initialization
- `ccp` initialized with SEV/PSP support
- `kvm_amd` reports `SEV-SNP enabled`

If these are missing, host kernel or firmware is not ready for SNP.

## KVM/SEV Device Access

Ensure your user can access KVM (and SEV when exposed):

```bash
groups $USER | grep kvm
ls -l /dev/kvm
ls -l /dev/sev
```

If `/dev/sev` exists but is not accessible, fix group/udev permissions as needed.

## Kernel/QEMU Compatibility Notes

SNP support depends on a compatible combination of:

- Host kernel (KVM/SEV-SNP support)
- QEMU build (IGVM/SNP features)
- Firmware (OVMF)

When the default distro stack is insufficient, use project bootstrap tooling first:

```bash
cargo run --bin xtask -- bootstrap-qemu
cargo run --bin xtask -- bootstrap-ovmf
```

Then run with the SNP config:

```bash
cargo run --bin xtask -- --target-arch snp qemu --config-path .config/qemu.snp.config.toml
```

## Common Error Pattern

Example symptom:

```text
qemu-system-x86_64: -accel kvm: check_sev_features: ... unsupported sev_features ...
qemu-system-x86_64: -accel kvm: failed to initialize kvm: Operation not permitted
```

Usually this points to host kernel/QEMU mismatch or missing permissions.

## Recommended Debug Path

1. Re-check `dmesg` capability signals.
2. Re-check `/dev/kvm` and `/dev/sev` permissions.
3. Confirm QEMU binary (`QEMU_BIN` or `tools/bin/qemu-system-x86_64`).
4. Re-run with `.config/qemu.snp.config.toml`.

If still failing, collect:

- `dmesg` SNP-related lines
- full QEMU command
- `qemu.log`

and continue in [Debug.md](Debug.md).
