#!/bin/bash

DEST=~/.local/

mkdir -p build

pushd build > /dev/null
git clone https://github.com/microsoft/igvm.git || true

pushd igvm > /dev/null
rustup override set stable
make -f igvm_c/Makefile
sudo make -f igvm_c/Makefile install
popd > /dev/null

git clone https://github.com/coconut-svsm/qemu || true

pushd qemu > /dev/null
git checkout svsm-igvm

PKG_CONFIG_PATH="/usr/lib64/pkgconfig:${PKG_CONFIG_PATH}" ./configure --target-list=x86_64-softmmu --prefix=$DEST --disable-werror --enable-igvm
PKG_CONFIG_PATH="/usr/lib64/pkgconfig:${PKG_CONFIG_PATH}" ninja -C build/ && make install

popd > /dev/null
popd > /dev/null