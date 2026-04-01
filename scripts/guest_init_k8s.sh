#!/bin/bash

DEKO_MODULE_PATH="${HOME}/deko-work/deko-lkm"

pushd ${DEKO_MODULE_PATH}
make clean
make -j
sudo insmod deko.ko
popd

minikube start --extra-config=kubeadm.ignore-preflight-errors=NumCPU --force --cpus=1 --driver=docker
minikube cp ${DEKO_MODULE_PATH}/deko.ko /tmp/deko.ko

minikube ssh -- 'minor=$(awk '\''$2 == "deko" { print $1 }'\'' /proc/misc); sudo rm -f /dev/deko; sudo mknod /dev/deko c 10 "$minor"; sudo chmod 600 /dev/deko; ls -l /dev/deko'

