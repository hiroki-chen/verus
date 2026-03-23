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

The image also includes:

- `gdb`
- `strace`
- a minimal set of CPython build dependencies
- a minimal set of glibc build dependencies
- a helper script to build a debug CPython from source:
  - `/guest-tests/bin/build_cpython_debug`
- a helper script to build a debug glibc in an isolated prefix:
  - `/guest-tests/bin/build_glibc_debug`

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
docker run --rm guest-tests:local dlopen_smoke
docker run --rm guest-tests:local copy_reloc_smoke
docker run --rm guest-tests:local copy_reloc_smoke_nopie
docker run --rm guest-tests:local localtime_smoke
docker run --rm guest-tests:local localtime_smoke_nopie
docker run --rm guest-tests:local read_localtime_file_smoke
docker run --rm guest-tests:local read_localtime_file_smoke_nopie
docker run --rm guest-tests:local stdio_seek_read_smoke
docker run --rm guest-tests:local stdio_seek_read_smoke_nopie
docker run --rm guest-tests:local tz_globals_smoke
docker run --rm guest-tests:local tz_globals_smoke_nopie
docker run --rm guest-tests:local thread_local_smoke
docker run --rm guest-tests:local thread_local_smoke_nopie
docker run --rm guest-tests:local tls_smoke
docker run --rm guest-tests:local python_init_like_smoke
docker run --rm guest-tests:local python_init_like_smoke_nopie
docker run --rm guest-tests:local python_runtime_early_smoke
docker run --rm guest-tests:local python_runtime_early_smoke_nopie
docker run --rm guest-tests:local python_exec_like_smoke
docker run --rm guest-tests:local python_exec_like_smoke_nopie
docker run --rm guest-tests:local python_reloc_heavy_smoke
docker run --rm guest-tests:local python_reloc_heavy_smoke_nopie
docker run --rm guest-tests:local fs_json_smoke
docker run --rm guest-tests:local concurrency_smoke
docker run --rm guest-tests:local http_loopback_smoke
```

Run the non-trivial smoke scripts:

```bash
docker run --rm guest-tests:local sqlite_smoke
docker run --rm guest-tests:local jq_smoke
docker run --rm guest-tests:local python_simple_smoke
docker run --rm guest-tests:local python_smoke
docker run --rm guest-tests:local tar_smoke
docker run --rm guest-tests:local nontrivial_smoke
```

## Known Workarounds

- Python and the minimal `localtime_smoke` currently hit a guest-side glibc `tzset()` bug whenever the `TZ` environment variable is present and non-empty.
- As a temporary workaround, clear `TZ` when running Python or time/locale-sensitive reproducers:

```bash
docker run --rm -e TZ= --entrypoint /usr/bin/python3 guest-tests:local -E -S -c 'print("hi")'
docker run --rm -e TZ= --entrypoint /guest-tests/bin/localtime_smoke_nopie guest-tests:local
```

If you want to bypass the entrypoint and execute the binary path directly:

```bash
docker run --rm --entrypoint /guest-tests/bin/random_migrate guest-tests:local
```

To build a debug CPython inside the container:

```bash
docker run --rm -it --entrypoint /guest-tests/bin/build_cpython_debug guest-tests:local
```

This defaults to CPython `3.12.3` and installs it under:

```text
/opt/cpython-debug/3.12.3
```

You can override the version and install prefix:

```bash
docker run --rm -it \
  --entrypoint /guest-tests/bin/build_cpython_debug \
  guest-tests:local \
  3.12.3 /opt/cpython-debug/3.12.3
```

After that, a simple startup smoke looks like:

```bash
/opt/cpython-debug/3.12.3/bin/python3 -S -c 'print("hi")'
```

And to debug it directly:

```bash
gdb --args /opt/cpython-debug/3.12.3/bin/python3 -S -c 'print("hi")'
```

If you want to build a debug glibc inside the container without touching the system libc:

```bash
docker run --rm -it --entrypoint /guest-tests/bin/build_glibc_debug guest-tests:local
```

This defaults to glibc `2.39` and installs it under:

```text
/opt/glibc-debug/2.39
```

You can override the version and install prefix:

```bash
docker run --rm -it \
  --entrypoint /guest-tests/bin/build_glibc_debug \
  guest-tests:local \
  2.39 /opt/glibc-debug/2.39
```

The helper builds glibc with debug info and a release-like optimization level (`-O2 -g3`), because upstream glibc refuses completely unoptimized (`-O0`) builds and some subsystems are fragile under lower optimization settings.

Run a test against the custom loader with:

```bash
/opt/glibc-debug/2.39/lib/ld-linux-x86-64.so.2 \
  --library-path /opt/glibc-debug/2.39/lib \
  /guest-tests/bin/localtime_smoke_nopie
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
- `dlopen_smoke.c`
  - Exercises explicit dynamic loading with `dlopen`, `dlsym`, and `dlclose` against `libm.so.6`.
- `copy_reloc_smoke.c`
  - Exercises direct references to `__environ`, `stdin`, `stdout`, and `stderr` so the non-PIE variant can be checked for `COPY` relocations similar to `python3`.
- `localtime_smoke.c`
  - Exercises a minimal `setlocale + time + localtime_r + strftime` path to isolate the early libc time/locale initialization chain.
- `read_localtime_file_smoke.c`
  - Exercises the plain `openat + fstat + read + close` path on `/etc/localtime` to separate raw file I/O from `tzset()` parsing and timezone-state updates.
- `stdio_seek_read_smoke.c`
  - Exercises both `FILE* + fread + fseek + fread` and `fd + read + lseek + read` on `/etc/localtime`, including a `fread_unlocked` path that more closely matches glibc's `__tzfile_read()` second-header logic.
- `tz_globals_smoke.c`
  - Exercises `tzset()` plus direct reads of libc's exported timezone globals `tzname`, `timezone`, and `daylight`.
- `thread_local_smoke.c`
  - Exercises a single-threaded `__thread` variable to isolate plain ELF TLS from pthread runtime setup.
- `copy_reloc_smoke_nopie`
  - Builds the same copy-relocation test as a non-PIE executable to make `R_X86_64_COPY` relocations visible in the main ELF.
- `localtime_smoke_nopie`
  - Builds the same localtime test as a non-PIE executable to compare against `python3`'s executable shape.
- `read_localtime_file_smoke_nopie`
  - Builds the same `/etc/localtime` file-read test as a non-PIE executable for direct comparison against glibc's timezone file path.
- `stdio_seek_read_smoke_nopie`
  - Builds the same stdio-vs-fd seek/read comparison as a non-PIE executable so the exact executable shape can be held constant while isolating `FILE*` behavior.
- `tz_globals_smoke_nopie`
  - Builds the same timezone-globals test as a non-PIE executable to match the `python3` executable shape more closely.
- `thread_local_smoke_nopie`
  - Builds the same TLS test as a non-PIE executable to compare against Python's `ET_EXEC` startup path.
- `tls_smoke.c`
  - Exercises ELF TLS plus `pthread_create`/`pthread_join` to separate TLS/runtime issues from basic dynamic loading.
- `python_init_like_smoke.c`
  - Exercises a Python-startup-like mix of locale setup, `getrandom`, `readlink`, metadata lookups, directory scans, file reads, `sigaction`, and `mmap/mprotect`.
- `python_init_like_smoke_nopie`
  - Builds the same Python-like startup test as a non-PIE executable to compare loader behavior with `python3`.
- `python_runtime_early_smoke.c`
  - Exercises a narrower Python-early-runtime mix of `sigaction`, locale, `getenv/setenv`, `getrandom`, `clock_gettime`, `localtime_r`, `pthread_key_create`, `pthread_create`, `pthread_cond*`, and `sem_*`.
- `python_runtime_early_smoke_nopie`
  - Builds the same early-runtime test as a non-PIE executable to better match `python3`'s main executable shape.
- `python_exec_like_smoke.c`
  - Exercises a more Python-like main executable shape with `__thread` TLS, a large writable runtime blob, `libm`, `zlib`, `expat`, environment scanning, and `mmap/mprotect`.
- `python_exec_like_smoke_nopie`
  - Builds the same Python-exec-like test as a non-PIE executable to better match `python3`'s `ET_EXEC` startup path.
- `python_reloc_heavy_smoke.c`
  - Exercises a relocation-heavy Python-like executable with many imported libc entry points, TLS, a large writable runtime state, `libm`, `zlib`, `expat`, sockets, locale, directory scanning, and mapping changes.
- `python_reloc_heavy_smoke_nopie`
  - Builds the same relocation-heavy test as a non-PIE executable to push closer to `python3`'s main ELF shape.
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
- `python_simple_smoke`
  - Exercises Python interpreter startup, small-file I/O, JSON parsing, and hashing with a smaller dependency surface.
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
