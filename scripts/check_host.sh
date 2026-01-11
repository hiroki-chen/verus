#!/bin/bash

set -e

cpuid -1 | grep -q 'SEV-SNP' || {
    echo "SEV-SNP not supported on this host."
    exit 1
}

# Extract the eax result.
echo "Checking for SEV-SNP Guest MSR Intercept support..."
val=$(cpuid -r -1 -l 0x8000001f | grep -Po 'eax=\K0x[0-9a-f]+')
if [ $(( ($val >> 22) & 1 )) -eq 1 ]; then
    echo "SEV-SNP Guest MSR Intercept is supported on this host."
else
    echo "SEV-SNP Guest MSR Intercept is NOT supported on this host."
    exit 1
fi

echo "Checking Allowed SEV Features support."
if [ $(( ($val >> 27) & 1 )) -eq 1 ]; then
    echo "CPU supportes Allowed SEV Features."
else
    echo "CPU does NOT support Allowed SEV Features."
    exit 1
fi
