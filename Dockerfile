# Pull base image from Ubuntu 24.04
FROM ubuntu:24.04

SHELL ["/bin/bash", "-c"]
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
    wget \
    git \
    gcc-multilib

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- --default-toolchain nightly -y
ENV PATH="/root/.cargo/bin:${PATH}"

WORKDIR /root
RUN git clone https://github.com/hiroki-chen/verus.git --branch main
WORKDIR /root/verus/source
RUN rustup -V
RUN ./tools/get-z3.sh
RUN source ../tools/activate

ENV PATH="/root/verus/tools/vargo/target/release:${PATH}"
RUN vargo build --release
RUN touch /root/verus/source/target/release/verus-root

WORKDIR /app
# Install the required toolchain
RUN rustup -V
RUN curl --proto '=https' --tlsv1.2 -LsSf https://github.com/verus-lang/verusfmt/releases/download/v0.5.7/verusfmt-installer.sh | sh

ENV PATH="/root/verus/source/target/release:/root/verus/source:${PATH}"

# install rust-src for nightly
RUN rustup component add rust-src --toolchain nightly-2025-02-14
