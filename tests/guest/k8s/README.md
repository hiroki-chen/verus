# Orders Function Group Example

This directory contains a minimal K8s/FaaS-style example for one Deko policy
domain.

The business boundary is selected by the shared label:

- `data-storage=orders`

The function group contains three services:

- `orders-ingest`
- `orders-transform`
- `orders-writer`

They are deployed together in the `faas-orders` namespace and are expected to
belong to the same Deko domain.

## Files

- `orders_function_group.yaml`
  K8s resources for the namespace, config map, deployments, services, and a
  smoke-test job.
- `orders_policy.toml`
  Example policy for the `orders` domain.
- `Dockerfile.orders-function`
  Shared image build file for the Python handlers.
- `../../deko-agent/deko_agent.py`
  Prototype guest-side attribution agent for turning `data-storage` labels into
  `mnt_ns_id -> domain_id` bindings.
- `../../deko-agent/Dockerfile`
  Minimal image for the prototype agent.
- `deko_agent_daemonset.yaml`
  Example `DaemonSet` + RBAC for running one attribution agent per node.

## Python handlers

The deployed handlers are:

- `tests/guest/scripts/orders_ingest.py`
- `tests/guest/scripts/orders_transform.py`
- `tests/guest/scripts/orders_writer.py`

Each service listens on port `8080` and exposes:

- `GET /healthz`
- `POST /orders` for ingest
- `POST /transform` for transform
- `POST /write` for writer

## Deploy With Minikube

From the repository root:

```bash
cd /home/haobchen/cage-sev
eval "$(minikube docker-env)"
```

Build the three images inside Minikube's Docker environment:

```bash
docker build -f tests/guest/k8s/Dockerfile.orders-function \
  --build-arg SCRIPT_PATH=scripts/orders_ingest.py \
  -t orders-ingest:latest .

docker build -f tests/guest/k8s/Dockerfile.orders-function \
  --build-arg SCRIPT_PATH=scripts/orders_transform.py \
  -t orders-transform:latest .

docker build -f tests/guest/k8s/Dockerfile.orders-function \
  --build-arg SCRIPT_PATH=scripts/orders_writer.py \
  -t orders-writer:latest .
```

Apply the resources:

```bash
kubectl apply -f tests/guest/k8s/orders_function_group.yaml
```

Wait for the three deployments:

```bash
kubectl -n faas-orders wait --for=condition=available deployment/orders-ingest --timeout=120s
kubectl -n faas-orders wait --for=condition=available deployment/orders-transform --timeout=120s
kubectl -n faas-orders wait --for=condition=available deployment/orders-writer --timeout=120s
```

Run and inspect the smoke test:

```bash
kubectl -n faas-orders delete job orders-pipeline-smoke --ignore-not-found
kubectl apply -f tests/guest/k8s/orders_function_group.yaml
kubectl -n faas-orders wait --for=condition=complete job/orders-pipeline-smoke --timeout=120s
kubectl -n faas-orders logs job/orders-pipeline-smoke
```

## Inspect Results

Show all resources:

```bash
kubectl get all -n faas-orders
```

Inspect logs:

```bash
kubectl -n faas-orders logs deploy/orders-ingest
kubectl -n faas-orders logs deploy/orders-transform
kubectl -n faas-orders logs deploy/orders-writer
```

Inspect the persisted output:

```bash
kubectl -n faas-orders exec deploy/orders-writer -- ls -l /tmp/orders-db
kubectl -n faas-orders exec deploy/orders-writer -- cat /tmp/orders-db/ord-1001.json
```

## Clean Up

Delete all resources from the example:

```bash
kubectl delete -f tests/guest/k8s/orders_function_group.yaml
```

## Prototype Guest Agent

`deko-agent/deko_agent.py` currently does this:

1. Watches Pods scheduled onto the local node.
2. Reads the Pod label `data-storage=...`.
3. Resolves each container's host PID by scanning host `/proc/*/cgroup` for the
   container ID.
4. Reads `/proc/<pid>/ns/mnt` to obtain `mnt_ns_id`.
5. Computes a temporary `domain_id` as `sha256(data-storage)[0..4]`.
6. Calls `/dev/deko` to register `mnt_ns_id -> domain_id`.
7. Optionally appends a JSONL debug record to a host file.

The JSONL output shape is:

```json
{
  "namespace": "faas-orders",
  "pod": "orders-ingest-...",
  "uid": "...",
  "data_storage": "orders",
  "domain_id": 1611977249,
  "container_id": "...",
  "pid": 12345,
  "mnt_ns_id": 4026532846
}
```

### Run Once On A Node

The prototype expects:

- service-account access to list Pods
- visibility into the host `/proc`
- access to the host `/dev/deko` char device

Example one-shot run:

```bash
sudo python3 deko-agent/deko_agent.py \
  --node-name "$(kubectl get pod -n kube-system -o wide | awk 'NR==2 {print $7}')" \
  --bindings-file /tmp/deko-domain-bindings.jsonl \
  --proc-root /proc \
  --device-path /dev/deko \
  --once
```

### Build And Deploy The Prototype DaemonSet

Before deploying the `DaemonSet`, make sure the prototype `/dev/deko` device
exists on the node host:

```bash
cd /home/haobchen/cage-sev/deko-lkm
make
sudo insmod deko.ko
ls -l /dev/deko
```

Build the agent image inside Minikube's Docker environment:

```bash
cd /home/haobchen/cage-sev
eval "$(minikube docker-env)"

docker build -f tests/guest/k8s/Dockerfile.deko-agent \
  -t deko-agent:latest .
```

Apply the `DaemonSet`:

```bash
kubectl apply -f tests/guest/k8s/deko_agent_daemonset.yaml
kubectl -n deko-system rollout status daemonset/deko-agent --timeout=120s
kubectl -n deko-system logs daemonset/deko-agent
```

If the `orders` example is already deployed, the agent should start emitting
lines similar to:

```text
[deko-agent] registered pod=orders-ingest-... data-storage=orders domain_id=... mnt_ns_id=...
```

You can also confirm the kernel side saw the ioctl:

```bash
dmesg | tail -n 50
```

Expected lines:

```text
deko: bind mnt_ns_id=... domain_id=...
```

Current limitation:

- the prototype `DaemonSet` derives `domain_id` from `data-storage` locally
- it does not yet perform signed endorsement validation
- it currently talks to the prototype `/dev/deko` LKM, not the final Linux
  path that `report_app` will query

## Agent Source Layout

The example deployment files remain under `tests/guest/k8s/`, but the agent
itself now lives in the first-class component directory:

- `deko-agent/deko_agent.py`
- `deko-agent/Dockerfile`

This keeps:

- `deko-lkm/` for the guest-kernel `/dev/deko` interface
- `deko-agent/` for the guest userspace node-local daemon
- `tests/guest/k8s/` for example manifests and smoke tests
