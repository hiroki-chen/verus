# deko-agent

`deko-agent` is the guest-side node-local attribution component for Deko.

Current prototype responsibilities:

- watch Pods scheduled onto the local Kubernetes node
- read the workload selector label such as `data-storage=...`
- auto-load a policy blob from a namespaced K8s `ConfigMap`
- resolve container host PIDs by scanning host `/proc/*/cgroup`
- read `/proc/<pid>/ns/mnt` to obtain `mnt_ns_id`
- derive a temporary `domain_id` from `data-storage`
- prepare namespace/domain bindings for the future `/dev/deko` registration path

This directory exists to keep the agent as a first-class component, separate
from:

- `deko-lkm/` for guest-kernel interfaces such as `/dev/deko`
- `tests/guest/k8s/` for example deployments and smoke tests

The current prototype implementation is Python. A Rust implementation skeleton
now also exists under:

- `deko-agent/Cargo.toml`
- `deko-agent/src/main.rs`
- `deko-agent/src/policy_compile.rs`
- `deko-agent/src/ioctl.rs`

The Rust path is the long-term implementation target.

## Rust Skeleton

The current Rust binary exposes these minimal commands:

```bash
cargo run --manifest-path deko-agent/Cargo.toml -- \
  compile-policy \
  --input tests/guest/k8s/projects/orders/policy.toml \
  --output /tmp/orders-policy.bin

cargo run --manifest-path deko-agent/Cargo.toml -- \
  load-policy \
  --device /dev/deko \
  --domain-id 471239387 \
  --policy-file tests/guest/k8s/projects/orders/policy.toml
```

For now this Rust binary covers:

- TOML lattice policy compilation into `deko-policy-format` binary blobs
- direct `/dev/deko` ioctl helpers for:
  - `load-policy`
  - `bind`
  - `lookup`
  - `unbind`

It does not yet replace the Python K8s watch/Pod scan loop.

## Prebuilt Rust Image

You can also package a host-built Rust `deko-agent` binary into a minimal
runtime image instead of compiling inside Docker.

Expected staging path:

- `deko-agent/dist/deko-agent`

Container build:

```bash
docker build -f deko-agent/Dockerfile.prebuilt \
  -t deko-agent-rust:latest \
  deko-agent
```

There is also a K8s-oriented wrapper Dockerfile at:

- `tests/guest/k8s/Dockerfile.deko-agent-prebuilt`

which expects the same staged binary in `deko-agent/dist/deko-agent`.

## Current `/dev/deko` Smoke Test

The current kernel module implementation is already slightly stronger than a
pure dummy handler:

- `bind` inserts `mnt_ns_id -> domain_id` into an in-kernel hash table
- `lookup` returns the stored mapping
- `unbind` removes the mapping
- bind/unbind also emit kernel log lines

So the simplest smoke test is:

1. load the module
2. issue `bind`
3. issue `lookup`
4. issue `unbind`
5. watch `dmesg`

Helper script:

- `deko-agent/dekoctl.py`

Example:

```bash
cd /home/haobchen/cage-sev
cd deko-lkm
make
sudo insmod deko.ko

sudo python3 /home/haobchen/cage-sev/deko-agent/dekoctl.py \
  bind --mnt-ns-id 12345 --domain-id 42

sudo python3 /home/haobchen/cage-sev/deko-agent/dekoctl.py \
  lookup --mnt-ns-id 12345

sudo python3 /home/haobchen/cage-sev/deko-agent/dekoctl.py \
  unbind --mnt-ns-id 12345 --domain-id 42

dmesg | tail -n 20
```

## Prototype Policy Load

The same helper can also push a policy blob into the monitor before apps from a
domain start registering:

```bash
sudo python3 /home/haobchen/cage-sev/deko-agent/dekoctl.py \
  load-policy \
  --domain-id 471239387 \
  --policy-file /home/haobchen/cage-sev/tests/guest/k8s/projects/orders/policy.toml
```

The expected order is:

1. load the policy for `domain_id`
2. bind `mnt_ns_id -> domain_id`
3. let the app `exec` path call `report_app`
