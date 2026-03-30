#!/usr/bin/env python3

import json
import os
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, HTTPServer


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


class OrdersIngestHandler(BaseHTTPRequestHandler):
    domain = os.environ.get("DATA_STORAGE", "orders")

    def do_GET(self) -> None:
        if self.path != "/healthz":
            self.send_error(404, "unknown path")
            return
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.end_headers()
        self.wfile.write(b"ok\n")

    def do_POST(self) -> None:
        if self.path != "/orders":
            self.send_error(404, "unknown path")
            return

        try:
            length = int(self.headers.get("Content-Length", "0"))
            payload = json.loads(self.rfile.read(length))
            order_id = str(payload.get("order_id", "")).strip()
            amount = int(payload.get("amount", 0))
            customer = str(payload.get("customer", "")).strip()
            if not order_id or amount <= 0:
                raise ValueError("invalid order payload")
        except Exception as exc:
            self.send_error(400, f"bad request: {exc}")
            return

        response = {
            "domain": self.domain,
            "stage": "orders-ingest",
            "order_id": order_id,
            "customer": customer,
            "amount": amount,
            "received_at": utc_now(),
            "next_handler": "orders-transform",
        }
        encoded = json.dumps(response).encode("utf-8")

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
    server = HTTPServer(addr, OrdersIngestHandler)
    print(f"orders-ingest listening on {addr[0]}:{addr[1]} domain={OrdersIngestHandler.domain}")
    server.serve_forever()


if __name__ == "__main__":
    main()
