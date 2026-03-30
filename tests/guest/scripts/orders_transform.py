#!/usr/bin/env python3

import json
import os
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, HTTPServer


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def risk_tier(amount: int) -> str:
    if amount >= 10_000:
        return "high"
    if amount >= 1_000:
        return "medium"
    return "low"


class OrdersTransformHandler(BaseHTTPRequestHandler):
    def do_GET(self) -> None:
        if self.path != "/healthz":
            self.send_error(404, "unknown path")
            return
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.end_headers()
        self.wfile.write(b"ok\n")

    def do_POST(self) -> None:
        if self.path != "/transform":
            self.send_error(404, "unknown path")
            return

        try:
            length = int(self.headers.get("Content-Length", "0"))
            payload = json.loads(self.rfile.read(length))
            order_id = str(payload.get("order_id", "")).strip()
            if not order_id:
                raise ValueError("missing order_id")

            result = {
                "domain": payload.get("domain", "orders"),
                "stage": "orders-transform",
                "order_id": order_id,
                "customer": str(payload.get("customer", "")).strip().upper(),
                "amount": int(payload.get("amount", 0)),
                "currency": "USD",
                "risk_tier": risk_tier(int(payload.get("amount", 0))),
                "normalized_at": utc_now(),
                "storage_target": "orders-writer",
            }
        except Exception as exc:
            self.send_error(400, f"bad request: {exc}")
            return

        encoded = json.dumps(result).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(encoded)))
        self.end_headers()
        self.wfile.write(encoded)

    def log_message(self, fmt: str, *args) -> None:
        return


def main() -> None:
    port = int(os.environ.get("PORT", "8080"))
    addr = ("0.0.0.0", port)
    server = HTTPServer(addr, OrdersTransformHandler)
    print(f"orders-transform listening on {addr[0]}:{addr[1]}")
    server.serve_forever()


if __name__ == "__main__":
    main()
