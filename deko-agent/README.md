# deko-agent

`deko-agent` is the guest-side node-local attribution component for Deko.

Current prototype responsibilities:

- watch Pods scheduled onto the local Kubernetes node
- read the workload selector label such as `data-storage=...`
- resolve container host PIDs through `crictl inspect`
- read `/proc/<pid>/ns/mnt` to obtain `mnt_ns_id`
- derive a temporary `domain_id` from `data-storage`
- prepare namespace/domain bindings for the future `/dev/deko` registration path

This directory exists to keep the agent as a first-class component, separate
from:

- `deko-lkm/` for guest-kernel interfaces such as `/dev/deko`
- `tests/guest/k8s/` for example deployments and smoke tests

The current prototype implementation is Python. The long-term implementation
target is Rust.

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
