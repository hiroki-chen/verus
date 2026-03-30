#!/bin/sh
set -eu

mnt_ns_id="$(stat -Lc %i /proc/self/ns/mnt)"
ready_dir="${DEKO_READY_DIR:-/deko-ready}"
ready_file="${ready_dir}/${mnt_ns_id}"
timeout_secs="${DEKO_BIND_TIMEOUT_SECS:-60}"

i=0
while [ "$i" -lt "$timeout_secs" ]; do
  if [ -f "${ready_file}" ]; then
    exec "$@"
  fi
  i=$((i + 1))
  sleep 1
done

echo "timeout waiting for deko bind: mnt_ns_id=${mnt_ns_id}" >&2
exit 1
