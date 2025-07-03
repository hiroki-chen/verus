#!/bin/bash

mkdir -p build

pushd build > /dev/null
git clone https://github.com/coconut-svsm/linux --single-branch -b svsm || true

pushd linux > /dev/null

# Configure the kernel configurations.

cp ../../.config/LINUX.config .config
make -j$(nproc) olddefconfig && make -j$(nproc)

popd > /dev/null
popd > /dev/null
