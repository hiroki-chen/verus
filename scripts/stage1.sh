#!/bin/bash

# First compile to an ELF object
as --32 \
   -o target/x86_64-tdx-deko/release/stage1.o deko-monitor/deko-stage1/stage1.S

ld -m elf_i386 -Tdeko-monitor/deko-stage1/stage1.lds \
   -o target/x86_64-tdx-deko/release/stage1.elf \
   target/x86_64-tdx-deko/release/stage1.o

# Then extract the raw binary
objcopy -O binary target/x86_64-tdx-deko/release/stage1.elf \
   target/x86_64-tdx-deko/release/stage1.bin
truncate -s 32K target/x86_64-tdx-deko/release/stage1.bin

td-shim-ld \
   target/x86_64-tdx-deko/release/ResetVector.bin target/x86_64-tdx-deko/release/deko-monitor \
   -t executable \
   -p target/x86_64-tdx-deko/release/deko-monitor \
   -o target/x86_64-tdx-deko/release/deko.bin
