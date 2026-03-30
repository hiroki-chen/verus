#!/usr/bin/env python3

import json
import mmap
import os
import socket
import tempfile
import time
from http.server import BaseHTTPRequestHandler, HTTPServer


def json_response(handler: BaseHTTPRequestHandler, status: int, payload: dict) -> None:
    body = json.dumps(payload).encode("utf-8")
    handler.send_response(status)
    handler.send_header("Content-Type", "application/json")
    handler.send_header("Content-Length", str(len(body)))
    handler.end_headers()
    handler.wfile.write(body)


def run_probe() -> dict:
    results: dict[str, object] = {}

    with tempfile.TemporaryDirectory(prefix="deko-syscalls-") as temp_dir:
        file_path = os.path.join(temp_dir, "payload.txt")
        fd = os.open(file_path, os.O_CREAT | os.O_RDWR | os.O_TRUNC, 0o600)
        try:
            os.write(fd, b"deko-syscalls\n")
            os.lseek(fd, 0, os.SEEK_SET)
            file_bytes = os.read(fd, 64)
            stat_result = os.fstat(fd)
        finally:
            os.close(fd)

        nested_dir = os.path.join(temp_dir, "nested")
        os.mkdir(nested_dir, 0o700)
        listing = sorted(os.listdir(temp_dir))

        read_fd, write_fd = os.pipe()
        try:
            os.write(write_fd, b"pipe-ok")
            pipe_bytes = os.read(read_fd, 32)
        finally:
            os.close(read_fd)
            os.close(write_fd)

        left, right = socket.socketpair()
        try:
            left.sendall(b"socket-ok")
            socket_bytes = right.recv(32)
        finally:
            left.close()
            right.close()

        with mmap.mmap(-1, 32) as mm:
            mm.write(b"mmap-ok")
            mm.seek(0)
            mmap_bytes = mm.read(7)

        os.unlink(file_path)
        os.rmdir(nested_dir)

    results["process"] = {
        "pid": os.getpid(),
        "ppid": os.getppid(),
        "uid": os.getuid(),
        "gid": os.getgid(),
    }
    results["filesystem"] = {
        "read_back": file_bytes.decode("utf-8").strip(),
        "size": stat_result.st_size,
        "listing": listing,
    }
    results["pipe"] = pipe_bytes.decode("utf-8")
    results["socketpair"] = socket_bytes.decode("utf-8")
    results["mmap"] = mmap_bytes.decode("utf-8")
    results["timing"] = {
        "monotonic_ns": time.monotonic_ns(),
        "clock_realtime_ns": time.clock_gettime_ns(time.CLOCK_REALTIME),
    }
    return results


class Handler(BaseHTTPRequestHandler):
    def do_GET(self) -> None:
        if self.path == "/healthz":
            json_response(self, 200, {"ok": True})
            return
        json_response(self, 404, {"error": "not found"})

    def do_POST(self) -> None:
        if self.path != "/probe":
            json_response(self, 404, {"error": "not found"})
            return
        try:
            payload = run_probe()
        except Exception as err:  # pragma: no cover - smoke endpoint
            json_response(self, 500, {"error": str(err)})
            return
        json_response(self, 200, payload)

    def log_message(self, format: str, *args: object) -> None:
        return


def main() -> None:
    port = int(os.environ.get("PORT", "8080"))
    server = HTTPServer(("0.0.0.0", port), Handler)
    server.serve_forever()


if __name__ == "__main__":
    main()
