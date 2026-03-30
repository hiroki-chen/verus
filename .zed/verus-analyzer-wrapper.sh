#!/usr/bin/env bash

export RUSTUP_TOOLCHAIN="1.79.0-x86_64-unknown-linux-gnu"

exec /usr/local/bin/verus-analyzer "$@"
