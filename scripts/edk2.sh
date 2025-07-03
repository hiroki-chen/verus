#!/bin/bash
SUBHOOK=https://github.com/tianocore/edk2-subhook.git

mkdir -p build

pushd build > /dev/null

git clone https://github.com/coconut-svsm/edk2.git --single-branch -b svsm || true

pushd edk2 > /dev/null


git submodule update --init --recursive
PYTHON3_ENABLE=TRUE PYTHON_COMMAND=python3 make -j $(getconf _NPROCESSORS_ONLN) -C BaseTools
. ./edksetup.sh --reconfig
build -a X64 -b DEBUG -t GCC5 -D DEBUG_ON_SERIAL_PORT -D DEBUG_VERBOSE -DTPM2_ENABLE -p OvmfPkg/OvmfPkgX64.dsc

mkdir -p ~/.local/share/ovmf
cp Build/OvmfX64/DEBUG_GCC5/FV/OVMF.fd ~/.local/share/ovmf/OVMF.fd

popd > /dev/null
popd > /dev/null
