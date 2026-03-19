# Guest Tests

This document covers the local SNP QEMU config layout and the current `tests/guest` workflow.

## QEMU Config Layout

The SNP QEMU config is split into two files:

- `.config/qemu.snp.template.toml`
  - Checked into git.
  - Uses placeholder paths only.
- `.config/qemu.snp.toml`
  - Local machine config.
  - Ignored by git.
  - This is the file used by `cargo qemu-snp`.

To create a local config from the template:

```bash
cp .config/qemu.snp.template.toml .config/qemu.snp.toml
```

Then update the local paths in `.config/qemu.snp.toml`.

Useful aliases:

```bash
cargo qemu-snp
cargo qemu-snp-template
```

- `cargo qemu-snp` uses `.config/qemu.snp.toml`
- `cargo qemu-snp-template` uses `.config/qemu.snp.template.toml`

## Shared Guest Test Directory

The local SNP config exports `tests/guest` into the guest over `virtfs` with mount tag `guest_tests`.

Before running the guest tests, enable VMPL trampoline support inside the guest:

```bash
sudo sh -c 'echo 1 > /sys/module/exec/parameters/vmpl_tramp'
```

Inside the guest:

```bash
mkdir -p /mnt/guest-tests
mount -t 9p -o trans=virtio,version=9p2000.L guest_tests /mnt/guest-tests
```

After mounting, the host directory:

```text
/home/haobchen/cage-sev/tests/guest
```

is visible inside the guest at:

```text
/mnt/guest-tests
```

This makes it easy to iterate on guest-side test sources without rebuilding the guest disk image.

## Guest Test Docker Image

The guest test Dockerfile lives at:

- `tests/guest/Dockerfile`

It now builds all C tests under `tests/guest/func` with `gcc` during image build and places the resulting binaries in `/guest-tests/bin`.

The runtime entrypoint is:

- `tests/guest/run-test.sh`

Default behavior:

- Start `passive_migrate`

You can build the image with:

```bash
docker build -t guest-tests:local tests/guest
```

List compiled tests:

```bash
docker run --rm guest-tests:local list
```

Run the passive migration test:

```bash
docker run --rm guest-tests:local passive_migrate
```

Run the active random migration test:

```bash
docker run --rm guest-tests:local random_migrate
```

Run any compiled test binary directly by name:

```bash
docker run --rm guest-tests:local sched
docker run --rm guest-tests:local while
docker run --rm guest-tests:local malloc_basic
docker run --rm guest-tests:local malloc_churn
```

If you want to bypass the entrypoint and execute the binary path directly:

```bash
docker run --rm --entrypoint /guest-tests/bin/random_migrate guest-tests:local
```

## Current Guest C Tests

The current C tests under `tests/guest/func` include:

- `passive_migrate.c`
  - Encourages scheduler-driven passive migration with busy work, `sched_yield()`, and short sleeps.
- `random_migrate.c`
  - Forces active migration by repeatedly choosing a random online CPU and calling `sched_setaffinity()`.
- `malloc_basic.c`
  - Verifies `malloc`, `calloc`, `realloc`, and `free` with data-preservation checks.
- `malloc_churn.c`
  - Repeatedly allocates, resizes, touches, and frees heap blocks across a wide size range.
- `sched.c`
- `while.c`

## Typical Flow

Build and launch QEMU with the local config:

```bash
cargo qemu-snp
```

Inside the guest, mount the shared guest test folder:

```bash
sudo sh -c 'echo 1 > /sys/module/exec/parameters/vmpl_tramp'
mkdir -p /mnt/guest-tests
mount -t 9p -o trans=virtio,version=9p2000.L guest_tests /mnt/guest-tests
```

Then either:

1. Build and run tests through Docker, or
2. Compile the C files directly inside the guest with `gcc`

For direct compilation inside the guest:

```bash
cd /mnt/guest-tests/func
gcc -O2 -Wall -Wextra -o passive_migrate passive_migrate.c
gcc -O2 -Wall -Wextra -o random_migrate random_migrate.c
gcc -O2 -Wall -Wextra -o malloc_basic malloc_basic.c
gcc -O2 -Wall -Wextra -o malloc_churn malloc_churn.c
./passive_migrate
./random_migrate
./malloc_basic
./malloc_churn
```
