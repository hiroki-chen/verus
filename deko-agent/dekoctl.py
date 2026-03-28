#!/usr/bin/env python3

import argparse
import ctypes
import fcntl
import os
import struct
import sys


DEKO_IOC_MAGIC = 0xDD
_IOC_NRBITS = 8
_IOC_TYPEBITS = 8
_IOC_SIZEBITS = 14
_IOC_DIRBITS = 2

_IOC_NRSHIFT = 0
_IOC_TYPESHIFT = _IOC_NRSHIFT + _IOC_NRBITS
_IOC_SIZESHIFT = _IOC_TYPESHIFT + _IOC_TYPEBITS
_IOC_DIRSHIFT = _IOC_SIZESHIFT + _IOC_SIZEBITS

_IOC_NONE = 0
_IOC_WRITE = 1
_IOC_READ = 2

BINDING_STRUCT = struct.Struct("=QII")
LOOKUP_STRUCT = struct.Struct("=QII")
LOAD_POLICY_STRUCT = struct.Struct("=IIQQ")


def _ioc(direction: int, ioc_type: int, nr: int, size: int) -> int:
    return (
        (direction << _IOC_DIRSHIFT)
        | (ioc_type << _IOC_TYPESHIFT)
        | (nr << _IOC_NRSHIFT)
        | (size << _IOC_SIZESHIFT)
    )


def _iow(ioc_type: int, nr: int, size: int) -> int:
    return _ioc(_IOC_WRITE, ioc_type, nr, size)


def _iowr(ioc_type: int, nr: int, size: int) -> int:
    return _ioc(_IOC_READ | _IOC_WRITE, ioc_type, nr, size)


DEKO_IOC_BIND_DOMAIN = _iow(DEKO_IOC_MAGIC, 0x01, BINDING_STRUCT.size)
DEKO_IOC_LOOKUP_DOMAIN = _iowr(DEKO_IOC_MAGIC, 0x02, LOOKUP_STRUCT.size)
DEKO_IOC_UNBIND_DOMAIN = _iow(DEKO_IOC_MAGIC, 0x03, BINDING_STRUCT.size)
DEKO_IOC_LOAD_POLICY = _iow(DEKO_IOC_MAGIC, 0x04, LOAD_POLICY_STRUCT.size)


def open_device(path: str) -> int:
    return os.open(path, os.O_RDWR)


def bind_domain(fd: int, mnt_ns_id: int, domain_id: int) -> None:
    payload = BINDING_STRUCT.pack(mnt_ns_id, domain_id, 0)
    fcntl.ioctl(fd, DEKO_IOC_BIND_DOMAIN, payload)


def lookup_domain(fd: int, mnt_ns_id: int) -> tuple[int, int]:
    payload = bytearray(LOOKUP_STRUCT.pack(mnt_ns_id, 0, 0))
    fcntl.ioctl(fd, DEKO_IOC_LOOKUP_DOMAIN, payload, True)
    _, domain_id, found = LOOKUP_STRUCT.unpack(payload)
    return domain_id, found


def unbind_domain(fd: int, mnt_ns_id: int, domain_id: int) -> None:
    payload = BINDING_STRUCT.pack(mnt_ns_id, domain_id, 0)
    fcntl.ioctl(fd, DEKO_IOC_UNBIND_DOMAIN, payload)


def load_policy(fd: int, domain_id: int, policy_bytes: bytes) -> None:
    policy_buf = ctypes.create_string_buffer(policy_bytes, len(policy_bytes))
    payload = LOAD_POLICY_STRUCT.pack(
        domain_id,
        0,
        ctypes.addressof(policy_buf),
        len(policy_bytes),
    )
    fcntl.ioctl(fd, DEKO_IOC_LOAD_POLICY, payload)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Minimal /dev/deko ioctl tester")
    parser.add_argument("--device", default="/dev/deko")
    subparsers = parser.add_subparsers(dest="command", required=True)

    bind_parser = subparsers.add_parser("bind")
    bind_parser.add_argument("--mnt-ns-id", type=int, required=True)
    bind_parser.add_argument("--domain-id", type=int, required=True)

    lookup_parser = subparsers.add_parser("lookup")
    lookup_parser.add_argument("--mnt-ns-id", type=int, required=True)

    unbind_parser = subparsers.add_parser("unbind")
    unbind_parser.add_argument("--mnt-ns-id", type=int, required=True)
    unbind_parser.add_argument("--domain-id", type=int, default=0)

    load_parser = subparsers.add_parser("load-policy")
    load_parser.add_argument("--domain-id", type=int, required=True)
    load_parser.add_argument("--policy-file", required=True)

    return parser


def main() -> int:
    args = build_parser().parse_args()
    fd = open_device(args.device)
    try:
        if args.command == "bind":
            bind_domain(fd, args.mnt_ns_id, args.domain_id)
            print(f"bound mnt_ns_id={args.mnt_ns_id} domain_id={args.domain_id}")
        elif args.command == "lookup":
            domain_id, found = lookup_domain(fd, args.mnt_ns_id)
            print(
                f"lookup mnt_ns_id={args.mnt_ns_id} found={found} domain_id={domain_id}"
            )
        elif args.command == "unbind":
            unbind_domain(fd, args.mnt_ns_id, args.domain_id)
            print(f"unbound mnt_ns_id={args.mnt_ns_id} domain_id={args.domain_id}")
        elif args.command == "load-policy":
            with open(args.policy_file, "rb") as f:
                policy_bytes = f.read()
            load_policy(fd, args.domain_id, policy_bytes)
            print(
                f"loaded policy domain_id={args.domain_id} "
                f"bytes={len(policy_bytes)} file={args.policy_file}"
            )
    finally:
        os.close(fd)
    return 0


if __name__ == "__main__":
    sys.exit(main())
