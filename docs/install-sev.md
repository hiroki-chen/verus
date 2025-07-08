# Preparation for AMD-SEV-SNP

This installation guide is for AMD SEV-SNP machines only. For TDX guests please refer to install-tdx.md.

## System Requirements

You would need to have a working AMD EPYC CPU that supports latest SNP features and has SNP firmware version > 1.51. The host kernel must also support the latest SNP features and SVSM supports.
You can check via the following command, and the expected output is also given.

```sh
sudo dmesg | egrep "SEV|RMP|ccp"                     
[    0.000000] SEV-SNP: RMP table physical range [0x0000000015600000 - 0x0000000075cfffff]
[    0.003653] SEV-SNP: Reserving start/end of RMP table on a 2MB boundary [0x0000000075c00000]
[    7.298333] ccp 0000:01:00.5: enabling device (0000 -> 0002)
[    7.300489] ccp 0000:01:00.5: sev enabled
[    7.300493] ccp 0000:01:00.5: psp enabled
[    7.300731] ccp 0000:83:00.5: enabling device (0000 -> 0002)
[    7.301616] ccp 0000:83:00.5: psp enabled
[   11.437438] ccp 0000:01:00.5: SEV API:1.55 build:37
[   11.437451] ccp 0000:01:00.5: SEV-SNP API:1.55 build:37
[   11.448630] kvm_amd: SEV enabled (ASIDs 100 - 1006)
[   11.448633] kvm_amd: SEV-ES enabled (ASIDs 1 - 99)
[   11.448636] kvm_amd: SEV-SNP enabled (ASIDs 1 - 99)
```

You should be able to see that both SEV, SEV-ES, and SEV-SNP are supported on the host machine. We recommend that you install the required host components via coconut-svsm, including the host kernel, hypervisor, and firmware. See [this](https://github.com/coconut-svsm/svsm/blob/main/Documentation/docs/installation/INSTALL.md). For convenience we also provided several wrapper scripts for building these components:

- `scripts/qemu.sh`
- `scripts/edk2.sh`
- `scripts/guest.sh`

Also, the host system must be Ubuntu 24.04 or higher; otherwise you may need to install dependencies to avoid incompatibility with builds which can be very hard to debug.