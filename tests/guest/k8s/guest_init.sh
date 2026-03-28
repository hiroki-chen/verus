#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "${SCRIPT_DIR}/../../.." && pwd)

WORK_ROOT="${WORK_ROOT:-$HOME/deko-work}"
MODULE_ROOT="${MODULE_ROOT:-${WORK_ROOT}/deko-lkm}"
MODULE_PATH="${MODULE_PATH:-${MODULE_ROOT}/deko.ko}"

CLUSTER_NAME="${CLUSTER_NAME:-minikube}"
MINIKUBE_DRIVER="${MINIKUBE_DRIVER:-docker}"
MINIKUBE_CPUS="${MINIKUBE_CPUS:-2}"
MINIKUBE_MEMORY_MB="${MINIKUBE_MEMORY_MB:-4096}"

log() {
  printf '[guest-init] %s\n' "$*"
}

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "Missing required command: $1" >&2
    exit 1
  }
}

ensure_module_exists() {
  if [[ ! -f "${MODULE_PATH}" ]]; then
    echo "Missing deko module: ${MODULE_PATH}" >&2
    echo "Build deko-lkm first under ${MODULE_ROOT}." >&2
    exit 1
  fi
}

start_cluster() {
  log "Starting Minikube (${CLUSTER_NAME})"
  minikube start \
    -p "${CLUSTER_NAME}" \
    --driver="${MINIKUBE_DRIVER}" \
    --cpus="${MINIKUBE_CPUS}" \
    --memory="${MINIKUBE_MEMORY_MB}"

  kubectl config use-context "${CLUSTER_NAME}" >/dev/null 2>&1 || true
}

build_images() {
  log "Building Rust deko-agent helper"
  cargo build-agent-debug

  log "Building latest Docker images in Minikube Docker"
  eval "$(minikube -p "${CLUSTER_NAME}" docker-env)"

  docker build -f "${REPO_ROOT}/tests/guest/k8s/Dockerfile.orders-function" \
    --build-arg SCRIPT_PATH=orders_ingest.py \
    -t orders-ingest:latest \
    "${REPO_ROOT}/tests/guest/scripts"

  docker build -f "${REPO_ROOT}/tests/guest/k8s/Dockerfile.orders-function" \
    --build-arg SCRIPT_PATH=orders_transform.py \
    -t orders-transform:latest \
    "${REPO_ROOT}/tests/guest/scripts"

  docker build -f "${REPO_ROOT}/tests/guest/k8s/Dockerfile.orders-function" \
    --build-arg SCRIPT_PATH=orders_writer.py \
    -t orders-writer:latest \
    "${REPO_ROOT}/tests/guest/scripts"

  docker build -f "${REPO_ROOT}/tests/guest/k8s/Dockerfile.deko-agent" \
    -t deko-agent:latest \
    "${REPO_ROOT}/deko-agent"
}

install_deko_module() {
  local remote_module="/tmp/deko.ko"

  log "Copying deko.ko into Minikube node"
  minikube -p "${CLUSTER_NAME}" cp "${MODULE_PATH}" "${remote_module}"

  log "Installing deko.ko in Minikube node"
  minikube -p "${CLUSTER_NAME}" ssh -- "sudo rmmod deko 2>/dev/null || true"
  minikube -p "${CLUSTER_NAME}" ssh -- "sudo insmod ${remote_module}"
  minikube -p "${CLUSTER_NAME}" ssh -- '
    set -eu
    minor=$(awk '"'"'$2 == "deko" { print $1 }'"'"' /proc/misc)
    if [ -z "${minor}" ]; then
      echo "failed to resolve deko misc minor" >&2
      exit 1
    fi
    sudo rm -f /dev/deko
    sudo mknod /dev/deko c 10 "${minor}"
    sudo chmod 600 /dev/deko
    ls -l /dev/deko
  '
}

apply_manifests() {
  log "Applying latest workload and agent manifests"
  kubectl apply -f "${REPO_ROOT}/tests/guest/k8s/orders_function_group.yaml"
  kubectl apply -f "${REPO_ROOT}/tests/guest/k8s/deko_agent_daemonset.yaml"

  kubectl -n faas-orders rollout status deployment/orders-ingest --timeout=120s
  kubectl -n faas-orders rollout status deployment/orders-transform --timeout=120s
  kubectl -n faas-orders rollout status deployment/orders-writer --timeout=120s
  kubectl -n deko-system rollout status daemonset/deko-agent --timeout=120s
}

print_summary() {
  cat <<EOF

guest_init complete.

Useful checks:

  kubectl get pods -A
  kubectl -n deko-system logs -l app.kubernetes.io/name=deko-agent
  kubectl -n faas-orders delete job orders-pipeline-smoke --ignore-not-found
  kubectl apply -f ${REPO_ROOT}/tests/guest/k8s/orders_function_group.yaml
  kubectl -n faas-orders wait --for=condition=complete job/orders-pipeline-smoke --timeout=120s
  kubectl -n faas-orders logs job/orders-pipeline-smoke
EOF
}

main() {
  require_cmd cargo
  require_cmd docker
  require_cmd kubectl
  require_cmd minikube
  ensure_module_exists
  start_cluster
  build_images
  install_deko_module
  apply_manifests
  print_summary
}

main "$@"
