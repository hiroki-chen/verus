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

# Install IGVMGEN
WORKDIR /root
RUN wget https://repo.anaconda.com/archive/Anaconda3-2025.06-0-Linux-x86_64.sh -O anaconda.sh
RUN bash anaconda.sh -b -p /opt/conda
ENV PATH="/opt/conda/bin:${PATH}"

RUN git clone https://github.com/hiroki-chen/igvm-tooling.git -b verismo-igvm
WORKDIR /root/igvm-tooling/src
RUN apt install -y acpica-tools bc
RUN pip3 install ./

WORKDIR /root
RUN git clone https://github.com/coconut-svsm/svsm.git
WORKDIR /root/svsm
# Clone packit
RUN git submodule update --init -- packit
RUN cargo install --path ./igvmbuilder --locked

WORKDIR /root
RUN git clone https://github.com/coconut-svsm/edk2.git --single-branch -b svsm
WORKDIR /root/edk2
RUN git submodule update --init --recursive
RUN apt install -y uuid-dev build-essential nasm ninja-build meson
RUN PYTHON3_ENABLE=TRUE PYTHON_COMMAND=python3 make -j $(getconf _NPROCESSORS_ONLN) -C BaseTools
RUN . ./edksetup.sh --reconfig && \
    build -a X64 -b DEBUG -t GCC5 -D DEBUG_ON_SERIAL_PORT -D DEBUG_VERBOSE -DTPM2_ENABLE -p OvmfPkg/OvmfPkgX64.dsc

RUN mkdir -p /root/ovmf
RUN cp Build/OvmfX64/DEBUG_GCC5/FV/OVMF.fd /root/ovmf/OVMF.fd

RUN apt install -y mtools dosfstools

WORKDIR /app
RUN rustup target add x86_64-unknown-uefi --toolchain nightly-2025-02-14
ENV PATH="/app/.bin:${PATH}"
