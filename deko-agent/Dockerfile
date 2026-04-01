FROM rust:1.94-bookworm AS builder

WORKDIR /build

COPY deko-policy-format /build/deko-policy-format
COPY deko-agent /build/deko-agent

WORKDIR /build/deko-agent
RUN cargo build --release

FROM debian:bookworm-slim

WORKDIR /app

COPY --from=builder /build/deko-agent/target/release/deko-agent /app/deko-agent

RUN chmod +x /app/deko-agent

ENTRYPOINT ["/app/deko-agent", "scan"]
