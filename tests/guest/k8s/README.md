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
