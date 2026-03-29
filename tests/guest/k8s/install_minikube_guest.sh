#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

KUBECTL_VERSION="${KUBECTL_VERSION:-v1.32.2}"
MINIKUBE_VERSION="${MINIKUBE_VERSION:-v1.35.0}"
CRICTL_VERSION="${CRICTL_VERSION:-v1.32.0}"
INSTALL_USER_NAME="${SUDO_USER:-$USER}"
INSTALL_USER_HOME=$(getent passwd "${INSTALL_USER_NAME}" | cut -d: -f6)

log() {
  printf '[install-minikube-guest] %s\n' "$*"
}

require_root() {
  if [[ ${EUID} -ne 0 ]]; then
    echo "Please run as root: sudo $0" >&2
    exit 1
  fi
}

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "Missing required command: $1" >&2
    exit 1
  }
}

apt_install() {
  DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends "$@"
}

install_base_packages() {
  log "Installing base packages"
  apt-get update
  apt_install \
    apt-transport-https \
    ca-certificates \
    conntrack \
    curl \
    gnupg \
    iptables \
    jq \
    socat \
    tar \
    docker.io
}

install_kubectl() {
  log "Installing kubectl ${KUBECTL_VERSION}"
  curl -fsSL "https://dl.k8s.io/release/${KUBECTL_VERSION}/bin/linux/amd64/kubectl" \
    -o /usr/local/bin/kubectl
  chmod 0755 /usr/local/bin/kubectl
}

install_minikube() {
  log "Installing minikube ${MINIKUBE_VERSION}"
  curl -fsSL \
    "https://storage.googleapis.com/minikube/releases/${MINIKUBE_VERSION}/minikube-linux-amd64" \
    -o /usr/local/bin/minikube
  chmod 0755 /usr/local/bin/minikube
}

install_crictl() {
  local tarball="/tmp/crictl-${CRICTL_VERSION}-linux-amd64.tar.gz"
  log "Installing crictl ${CRICTL_VERSION}"
  curl -fsSL \
    "https://github.com/kubernetes-sigs/cri-tools/releases/download/${CRICTL_VERSION}/crictl-${CRICTL_VERSION}-linux-amd64.tar.gz" \
    -o "${tarball}"
  tar -C /usr/local/bin -xzf "${tarball}" crictl
  rm -f "${tarball}"
  chmod 0755 /usr/local/bin/crictl
}

configure_docker() {
  log "Enabling docker service"
  systemctl enable --now docker
  usermod -aG docker "${INSTALL_USER_NAME}" || true
}

ensure_kernel_modules() {
  log "Loading common Minikube networking modules"
  modprobe overlay || true
  modprobe br_netfilter || true
}

write_sysctl_config() {
  log "Configuring sysctl for container networking"
  cat >/etc/sysctl.d/99-minikube-k8s.conf <<'EOF'
net.bridge.bridge-nf-call-iptables = 1
net.bridge.bridge-nf-call-ip6tables = 1
net.ipv4.ip_forward = 1
EOF
  sysctl --system >/dev/null
}

print_versions() {
  log "Installed tool versions"
  kubectl version --client --output=yaml || true
  minikube version || true
  crictl --version || true
  docker --version || true
}

print_next_steps() {
  cat <<EOF

Install complete.

Recommended next steps:

1. Re-login or run:
   newgrp docker

2. Start Minikube with the Docker driver:
   minikube start --driver=docker

3. Verify the cluster:
   kubectl get nodes

4. Build and deploy the Deko examples:
   cd ${SCRIPT_DIR%/tests/guest/k8s}
   eval "\$(minikube docker-env)"
   docker build -f tests/guest/k8s/shared/Dockerfile.python-service --build-arg SCRIPT_PATH=orders_ingest.py -t orders-ingest:latest tests/guest
   docker build -f tests/guest/k8s/shared/Dockerfile.python-service --build-arg SCRIPT_PATH=orders_transform.py -t orders-transform:latest tests/guest
   docker build -f tests/guest/k8s/shared/Dockerfile.python-service --build-arg SCRIPT_PATH=orders_writer.py -t orders-writer:latest tests/guest
   docker build -f tests/guest/k8s/shared/Dockerfile.python-service --build-arg SCRIPT_PATH=syscalls_probe.py -t syscalls-probe:latest tests/guest
   docker build -f tests/guest/k8s/Dockerfile.deko-agent -t deko-agent:latest deko-agent
   kubectl apply -f tests/guest/k8s/projects/orders/project.yaml
   kubectl apply -f tests/guest/k8s/projects/syscalls/project.yaml
   kubectl apply -f tests/guest/k8s/shared/deko_agent_daemonset.yaml

If you want to skip Docker and try Minikube's "none" driver, that is possible,
but this script optimizes for the Docker driver because it matches our current
K8s test workflow.
EOF
}

main() {
  require_root
  require_cmd curl
  require_cmd tar
  require_cmd systemctl
  require_cmd getent

  install_base_packages
  install_kubectl
  install_minikube
  install_crictl
  ensure_kernel_modules
  write_sysctl_config
  configure_docker
  print_versions
  print_next_steps
}

main "$@"
