# Pull base image from Ubuntu 24.04
FROM ubuntu:24.04

ARG HOST_UID=1000
ARG HOST_GID=1000

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
    gcc-multilib \
    mtools dosfstools

RUN groupadd -g ${HOST_GID} builder && \
    useradd -u ${HOST_UID} -g ${HOST_GID} -ms /bin/bash builder
RUN mkdir -p /app && chown builder:builder /app

WORKDIR /app
USER builder
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | \
    sh -s -- -y --default-toolchain nightly

WORKDIR /home/builder/.verus
RUN git clone https://github.com/hiroki-chen/verus.git
WORKDIR /home/builder/.verus/verus/source
ENV PATH="/home/builder/.cargo/bin:${PATH}"
RUN rustup -V
RUN ./tools/get-z3.sh
RUN source ../tools/activate

ENV PATH="/home/builder/.verus/verus/tools/vargo/target/release:${PATH}"
RUN vargo build --release
RUN touch /home/builder/.verus/verus/source/target/release/verus-root

# Install the required toolchain
RUN rustup -V
RUN curl --proto '=https' --tlsv1.2 -LsSf https://github.com/verus-lang/verusfmt/releases/download/v0.5.7/verusfmt-installer.sh | sh

ENV PATH="/home/builder/.verus/verus/source/target/release:/home/builder/.verus/verus/source:${PATH}"

# install rust-src for nightly
RUN rustup component add rust-src --toolchain nightly-2025-02-14
RUN rustup target add x86_64-unknown-uefi --toolchain nightly-2025-02-14
ENV PATH="/app/.bin:${PATH}"

WORKDIR /app
