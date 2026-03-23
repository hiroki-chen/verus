#!/usr/bin/env python3

import argparse
import json
import re
import sys
from pathlib import Path


ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
INVOKED_RE = re.compile(
    r"^\[INFO\]\s+\[CPU:(?P<cpu>\d+)\]\s+\[VMPL:(?P<vmpl>\d+)\]\s+.*Syscall invoked:\s+(?P<name>\S+)\s*$"
)
BODY_RE = re.compile(
    r"^\[INFO\]\s+\[CPU:(?P<cpu>\d+)\]\s+\[VMPL:(?P<vmpl>\d+)\]\s+.*Syscall body DekoSyscallBody \{$"
)
FIELD_RE = re.compile(r"^\s*(?P<key>[a-z0-9_]+):\s+0x(?P<value>[0-9A-Fa-f]+),?\s*$")


def strip_ansi(line: str) -> str:
    return ANSI_RE.sub("", line).rstrip("\n")


def parse_body(lines: list[str], start: int) -> tuple[dict[str, str], int]:
    fields: dict[str, str] = {}
    idx = start
    while idx < len(lines):
        line = lines[idx]
        if line.strip() == "}":
            return fields, idx + 1
        match = FIELD_RE.match(line)
        if match:
            fields[match.group("key")] = f"0x{match.group('value').lower()}"
        idx += 1
    return fields, idx


def extract_records(lines: list[str]) -> list[dict[str, object]]:
    records: list[dict[str, object]] = []
    idx = 0
    while idx < len(lines):
        line = lines[idx]
        invoked = INVOKED_RE.match(line)
        if not invoked:
            idx += 1
            continue

        record: dict[str, object] = {
            "cpu": int(invoked.group("cpu")),
            "vmpl": int(invoked.group("vmpl")),
            "syscall": invoked.group("name"),
        }

        if idx + 1 < len(lines):
            body = BODY_RE.match(lines[idx + 1])
            if body:
                fields, next_idx = parse_body(lines, idx + 2)
                record["body"] = fields
                idx = next_idx
                records.append(record)
                continue

        idx += 1
        records.append(record)
    return records


def render_plain(record: dict[str, object]) -> str:
    body = record.get("body")
    if not isinstance(body, dict):
        return f"cpu={record['cpu']} vmpl={record['vmpl']} syscall={record['syscall']}"

    ordered_keys = ["rax", "rdi", "rsi", "rdx", "r10", "r8", "r9", "rcx", "r11", "cr3"]
    rendered = [f"cpu={record['cpu']}", f"vmpl={record['vmpl']}", f"syscall={record['syscall']}"]
    for key in ordered_keys:
        if key in body:
            rendered.append(f"{key}={body[key]}")
    for key in sorted(body.keys()):
        if key not in ordered_keys:
            rendered.append(f"{key}={body[key]}")
    return " ".join(rendered)


def main() -> int:
    parser = argparse.ArgumentParser(description="Extract syscall traces from deko out.log")
    parser.add_argument("logfile", nargs="?", default="out.log", help="Path to the log file")
    parser.add_argument("--json", action="store_true", help="Emit JSON lines instead of plain text")
    args = parser.parse_args()

    log_path = Path(args.logfile)
    if not log_path.exists():
        print(f"log file not found: {log_path}", file=sys.stderr)
        return 1

    raw_lines = log_path.read_text(errors="replace").splitlines()
    lines = [strip_ansi(line) for line in raw_lines]
    records = extract_records(lines)

    for record in records:
        if args.json:
            print(json.dumps(record, sort_keys=True))
        else:
            print(render_plain(record))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
