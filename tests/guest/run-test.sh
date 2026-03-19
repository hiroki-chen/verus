#!/usr/bin/env bash

set -euo pipefail

BIN_DIR=/guest-tests/bin

if [[ $# -eq 0 ]]; then
  exec "${BIN_DIR}/passive_migrate"
fi

if [[ "$1" == "list" ]]; then
  exec ls -1 "${BIN_DIR}"
fi

if [[ -x "${BIN_DIR}/$1" ]]; then
  exec "${BIN_DIR}/$1" "${@:2}"
fi

exec "$@"
