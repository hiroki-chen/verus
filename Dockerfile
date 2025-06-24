# Pull base image from Ubuntu 24.04
FROM ubuntu:24.04

COPY . /app

RUN apt-get update
RUN apt-get install -y \
    build-essential \
    ninja-build \
    libclang-dev \
    libelf-dev \
    gcc-9 \
    cmake\
    bison \
    flex \
    unzip \
    curl \
    python3-pip \
    python3-venv \
    wget

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- --default-toolchain nightly -y

# Install Verus.
RUN wget https://github.com/verus-lang/verus/releases/download/release%2F0.2025.06.23.2e59154/verus-0.2025.06.23.2e59154-x86-linux.zip -O verus.zip
RUN unzip verus.zip -d /app/.bin
RUN rm verus.zip

ENV PATH="/app/.bin/verus-x86-linux:/app/.bin:/root/.cargo/bin:${PATH}"

WORKDIR /app
# Install the required toolchain
RUN rustup toolchain install nightly-2025-02-14
