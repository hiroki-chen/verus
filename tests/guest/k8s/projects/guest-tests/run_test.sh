#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <test-binary-name>" >&2
  exit 1
fi

test_name="$1"
namespace="faas-guest-tests"
pod_name="guest-tests-launcher"

kubectl apply -f tests/guest/k8s/projects/guest-tests/project.yaml >/dev/null
kubectl -n "$namespace" wait --for=condition=Ready "pod/${pod_name}" --timeout=120s >/dev/null

mnt_ns_link="$(kubectl -n "$namespace" exec "$pod_name" -- readlink /proc/self/ns/mnt)"
mnt_ns_id="${mnt_ns_link#mnt:[}"
mnt_ns_id="${mnt_ns_id%]}"

deadline=$((SECONDS + 120))
while (( SECONDS < deadline )); do
  if kubectl -n "$namespace" exec "$pod_name" -- cat "/deko-ready/${mnt_ns_id}" >/dev/null 2>&1; then
    exec kubectl -n "$namespace" exec "$pod_name" -- "/guest-tests/bin/${test_name}"
  fi
  sleep 1
done

echo "timed out waiting for deko bind for mnt_ns_id=${mnt_ns_id}" >&2
exit 1
