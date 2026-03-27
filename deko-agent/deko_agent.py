#!/usr/bin/env python3

import argparse
import fcntl
import hashlib
import json
import os
import ssl
import struct
import sys
import time
import urllib.parse
import urllib.request
from typing import Any


DEFAULT_TOKEN_PATH = "/var/run/secrets/kubernetes.io/serviceaccount/token"
DEFAULT_CA_PATH = "/var/run/secrets/kubernetes.io/serviceaccount/ca.crt"
DEFAULT_KUBE_HOST = "kubernetes.default.svc"
DEFAULT_KUBE_PORT = "443"

DEKO_IOC_MAGIC = 0xDD
_IOC_NRBITS = 8
_IOC_TYPEBITS = 8
_IOC_SIZEBITS = 14
_IOC_DIRBITS = 2
_IOC_NRSHIFT = 0
_IOC_TYPESHIFT = _IOC_NRSHIFT + _IOC_NRBITS
_IOC_SIZESHIFT = _IOC_TYPESHIFT + _IOC_TYPEBITS
_IOC_DIRSHIFT = _IOC_SIZESHIFT + _IOC_SIZEBITS
_IOC_WRITE = 1

BINDING_STRUCT = struct.Struct("=QII")


def log(message: str) -> None:
    print(f"[deko-agent] {message}", flush=True)


def stable_domain_id(data_storage: str) -> int:
    digest = hashlib.sha256(data_storage.encode("utf-8")).digest()
    return int.from_bytes(digest[:4], byteorder="big", signed=False)


def _ioc(direction: int, ioc_type: int, nr: int, size: int) -> int:
    return (
        (direction << _IOC_DIRSHIFT)
        | (ioc_type << _IOC_TYPESHIFT)
        | (nr << _IOC_NRSHIFT)
        | (size << _IOC_SIZESHIFT)
    )


def _iow(ioc_type: int, nr: int, size: int) -> int:
    return _ioc(_IOC_WRITE, ioc_type, nr, size)


DEKO_IOC_BIND_DOMAIN = _iow(DEKO_IOC_MAGIC, 0x01, BINDING_STRUCT.size)


def read_text(path: str) -> str:
    with open(path, "r", encoding="utf-8") as handle:
        return handle.read().strip()


def kube_api_url() -> str:
    host = os.environ.get("KUBERNETES_SERVICE_HOST", DEFAULT_KUBE_HOST)
    port = os.environ.get("KUBERNETES_SERVICE_PORT", DEFAULT_KUBE_PORT)
    return f"https://{host}:{port}"


def kube_context(token_path: str, ca_path: str) -> tuple[str, ssl.SSLContext]:
    token = read_text(token_path)
    context = ssl.create_default_context(cafile=ca_path)
    return token, context


def kube_get_json(path: str, token_path: str, ca_path: str) -> dict[str, Any]:
    token, context = kube_context(token_path, ca_path)
    request = urllib.request.Request(
        urllib.parse.urljoin(kube_api_url(), path),
        headers={"Authorization": f"Bearer {token}"},
    )
    with urllib.request.urlopen(request, context=context, timeout=10) as response:
        return json.load(response)


def fetch_local_node_pods(
    node_name: str, token_path: str, ca_path: str
) -> list[dict[str, Any]]:
    selector = urllib.parse.quote(f"spec.nodeName={node_name}", safe="")
    path = f"/api/v1/pods?fieldSelector={selector}"
    data = kube_get_json(path, token_path, ca_path)
    return data.get("items", [])


def extract_data_storage(pod: dict[str, Any]) -> str | None:
    metadata = pod.get("metadata", {})
    labels = metadata.get("labels", {})
    return labels.get("data-storage")


def list_container_ids(pod: dict[str, Any]) -> list[str]:
    status = pod.get("status", {})
    statuses = status.get("containerStatuses", [])
    container_ids: list[str] = []
    for entry in statuses:
        raw = entry.get("containerID", "")
        if "://" in raw:
            _, _, container_id = raw.partition("://")
            if container_id:
                container_ids.append(container_id)
    return container_ids


def proc_path(proc_root: str, *parts: str) -> str:
    return os.path.join(proc_root, *parts)


def read_proc_text(proc_root: str, pid: str, name: str) -> str:
    with open(proc_path(proc_root, pid, name), "r", encoding="utf-8", errors="ignore") as handle:
        return handle.read()


def pid_matches_container(proc_root: str, pid: str, container_id: str) -> bool:
    try:
        cgroup = read_proc_text(proc_root, pid, "cgroup")
    except OSError:
        return False

    short_id = container_id[:12]
    return container_id in cgroup or short_id in cgroup


def list_numeric_pids(proc_root: str) -> list[int]:
    pids: list[int] = []
    for entry in os.listdir(proc_root):
        if entry.isdigit():
            pids.append(int(entry))
    pids.sort()
    return pids


def resolve_container_pid(container_id: str, proc_root: str) -> int:
    matches: list[int] = []
    for pid in list_numeric_pids(proc_root):
        if pid_matches_container(proc_root, str(pid), container_id):
            matches.append(pid)

    if not matches:
        raise RuntimeError(f"unable to resolve pid for container {container_id}")

    return matches[0]


def read_mnt_ns_id(pid: int, proc_root: str) -> int:
    ns_path = proc_path(proc_root, str(pid), "ns", "mnt")
    return os.stat(ns_path).st_ino


def append_binding(path: str, binding: dict[str, Any]) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "a", encoding="utf-8") as handle:
        handle.write(json.dumps(binding, sort_keys=True))
        handle.write("\n")


def bind_namespace_domain(device_path: str, mnt_ns_id: int, domain_id: int) -> None:
    payload = BINDING_STRUCT.pack(mnt_ns_id, domain_id, 0)
    fd = os.open(device_path, os.O_RDWR)
    try:
        fcntl.ioctl(fd, DEKO_IOC_BIND_DOMAIN, payload)
    finally:
        os.close(fd)


def resolve_bindings_for_pod(pod: dict[str, Any], proc_root: str) -> list[dict[str, Any]]:
    data_storage = extract_data_storage(pod)
    if not data_storage:
        return []

    metadata = pod.get("metadata", {})
    bindings: list[dict[str, Any]] = []
    for container_id in list_container_ids(pod):
        pid = resolve_container_pid(container_id, proc_root)
        mnt_ns_id = read_mnt_ns_id(pid, proc_root)
        bindings.append(
            {
                "namespace": metadata.get("namespace"),
                "pod": metadata.get("name"),
                "uid": metadata.get("uid"),
                "data_storage": data_storage,
                "domain_id": stable_domain_id(data_storage),
                "container_id": container_id,
                "pid": pid,
                "mnt_ns_id": mnt_ns_id,
            }
        )
    return bindings


def binding_key(binding: dict[str, Any]) -> tuple[str, int, int]:
    return (
        str(binding["container_id"]),
        int(binding["mnt_ns_id"]),
        int(binding["domain_id"]),
    )


def run_once(args: argparse.Namespace) -> int:
    pods = fetch_local_node_pods(args.node_name, args.token_path, args.ca_path)
    total_bindings = 0
    new_bindings = 0
    for pod in pods:
        try:
            bindings = resolve_bindings_for_pod(pod, args.proc_root)
        except Exception as err:
            name = pod.get("metadata", {}).get("name", "<unknown>")
            log(f"skip pod {name}: {err}")
            continue

        for binding in bindings:
            total_bindings += 1
            key = binding_key(binding)
            if key in args.seen_bindings:
                continue

            bind_namespace_domain(args.device_path, binding["mnt_ns_id"], binding["domain_id"])
            if args.bindings_file:
                append_binding(args.bindings_file, binding)
            args.seen_bindings.add(key)
            new_bindings += 1
            log(
                "registered "
                f"pod={binding['pod']} data-storage={binding['data_storage']} "
                f"domain_id={binding['domain_id']} mnt_ns_id={binding['mnt_ns_id']}"
            )

    log(
        "completed scan: "
        f"observed {total_bindings} binding(s), "
        f"registered {new_bindings} new binding(s)"
    )
    return 0


def run_loop(args: argparse.Namespace) -> int:
    while True:
        run_once(args)
        time.sleep(args.interval_sec)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Prototype Deko guest-side namespace/domain attribution agent."
    )
    parser.add_argument(
        "--node-name",
        default=os.environ.get("NODE_NAME"),
        help="Current Kubernetes node name. Usually injected through the Downward API.",
    )
    parser.add_argument(
        "--bindings-file",
        default=os.environ.get(
            "DEKO_BINDINGS_FILE", "/host/tmp/deko-domain-bindings.jsonl"
        ),
        help="Optional JSONL debug log for resolved bindings.",
    )
    parser.add_argument(
        "--proc-root",
        default=os.environ.get("DEKO_HOST_PROC", "/host/proc"),
        help="Host /proc mount used to resolve mount-namespace inodes.",
    )
    parser.add_argument(
        "--device-path",
        default=os.environ.get("DEKO_DEVICE_PATH", "/host/dev/deko"),
        help="Path to the mounted /dev/deko char device.",
    )
    parser.add_argument("--token-path", default=DEFAULT_TOKEN_PATH)
    parser.add_argument("--ca-path", default=DEFAULT_CA_PATH)
    parser.add_argument("--interval-sec", type=int, default=15)
    parser.add_argument(
        "--once",
        action="store_true",
        help="Run a single scan instead of polling forever.",
    )
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if not args.node_name:
        parser.error("--node-name is required")
    args.seen_bindings = set()
    if args.once:
        return run_once(args)
    return run_loop(args)


if __name__ == "__main__":
    sys.exit(main())
