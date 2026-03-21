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

Reduce log volume by passing a larger `log_every` argument:

```bash
docker run --rm guest-tests:local random_migrate 20000000 0 512
docker run --rm guest-tests:local passive_migrate 50000000 1024
docker run --rm guest-tests:local malloc_churn 20000 0 4096
```

Run any compiled test binary directly by name:

```bash
docker run --rm guest-tests:local sched
docker run --rm guest-tests:local while
docker run --rm guest-tests:local malloc_basic
docker run --rm guest-tests:local malloc_churn
docker run --rm guest-tests:local fs_smoke
docker run --rm guest-tests:local mmap_file_smoke
docker run --rm guest-tests:local stdio_sort_smoke
docker run --rm guest-tests:local fs_json_smoke
docker run --rm guest-tests:local concurrency_smoke
docker run --rm guest-tests:local http_loopback_smoke
```

Run the non-trivial smoke scripts:

```bash
docker run --rm guest-tests:local sqlite_smoke
docker run --rm guest-tests:local jq_smoke
docker run --rm guest-tests:local python_smoke
docker run --rm guest-tests:local tar_smoke
docker run --rm guest-tests:local nontrivial_smoke
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
- `fs_smoke.c`
  - Exercises `mkdir`, `open`, `read/write`, `rename`, `stat`, `readdir`, and recursive cleanup on a small directory tree.
- `mmap_file_smoke.c`
  - Exercises `mkstemp`, `ftruncate`, `mmap`, `msync`, `mprotect`, `pread`, and `munmap` on a multi-page file.
- `stdio_sort_smoke.c`
  - Uses stdio plus heap allocation to write, parse, sort, rewrite, and re-read a structured dataset.
- `sched.c`
- `while.c`

The current Go tests under `tests/guest/go` include:

- `fs_json_smoke.go`
  - Exercises Go runtime startup, file I/O, JSON marshal/unmarshal, and slice growth.
- `concurrency_smoke.go`
  - Exercises goroutines, channels, synchronization, and heap activity across many tasks.
- `http_loopback_smoke.go`
  - Exercises Go networking, loopback TCP, `net/http`, JSON encoding/decoding, and request handling.

The current shell-based smoke scripts under `tests/guest/scripts` include:

- `sqlite_smoke`
  - Creates a SQLite database, performs inserts and updates, and runs `PRAGMA integrity_check`.
- `jq_smoke`
  - Parses and transforms structured JSON with `jq` and validates the summary output.
- `python_smoke`
  - Exercises Python runtime startup, JSON handling, file I/O, `mmap`, and hashing.
- `tar_smoke`
  - Packs and unpacks a small file tree and verifies extracted contents by `sha256sum`.
- `nontrivial_smoke`
  - Runs the four scripts above in sequence.

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
