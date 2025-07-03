#!/bin/bash

KERNEL=build/linux/arch/x86/boot/bzImage
DEKO=target/x86_64-sev-deko/release/deko-monitor
OUTPUT=target/x86_64-sev-deko/release/deko.igvm
OVMF=/root/ovmf/OVMF.fd

igvmbuilder \
  --sort \
  --policy 0x3000 \
  --kernel ${KERNEL} \
  --stage2 ${DEKO} \
  --output ${OUTPUT} \
  --firmware ${OVMF} \
  qemu \
  --snp