 #!/bin/bash

ESP_DIR="esp"
ESP_IMG="boot.img"

pushd target/x86_64-unknown-uefi/release > /dev/null

dd if=/dev/zero of=${ESP_IMG} bs=1M count=64

mkfs.fat -F 32 ${ESP_IMG}

mmd -i ${ESP_IMG} ::/EFI
mmd -i ${ESP_IMG} ::/EFI/BOOT
mcopy -i ${ESP_IMG} deko-stage1.efi ::/EFI/BOOT/BOOTX64.EFI

cp ${ESP_IMG} ../../x86_64-tdx-deko/release/

popd > /dev/null
