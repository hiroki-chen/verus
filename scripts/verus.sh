#!/bin/bash

pushd ~

git clone https://github.com/hiroki-chen/verus.git

pushd verus

bash -c tools/get-z3.sh
pushd source

. ../tools/activate
rustup toolchain install

vargo build --release

popd