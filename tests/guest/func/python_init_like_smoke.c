/*
 * Python-startup-like smoke test.
 *
 * This is not CPython itself, but it exercises a similar early-userspace mix:
 * locale setup, getrandom, readlink, file metadata lookups, directory scans,
 * small file reads, signal registration, and mmap/mprotect.
 */

#define _GNU_SOURCE

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <locale.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/random.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <unistd.h>

static void die_perror(const char *what) {
  perror(what);
  exit(1);
}

static void require_path(const char *path) {
  struct stat st;

  if (stat(path, &st) != 0)
    die_perror(path);
}

static size_t scan_dir(const char *path) {
  DIR *dir;
  struct dirent *ent;
  size_t count = 0;

  dir = opendir(path);
  if (!dir)
    die_perror(path);

  while ((ent = readdir(dir)) != NULL) {
    if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0)
      continue;
    count++;
  }

  if (closedir(dir) != 0)
    die_perror("closedir");

  return count;
}

static uint64_t read_file_checksum(const char *path, size_t limit) {
  char buf[4096];
  uint64_t checksum = 0;
  size_t total = 0;
  int fd;

  fd = open(path, O_RDONLY | O_CLOEXEC);
  if (fd < 0)
    die_perror(path);

  while (total < limit) {
    size_t want = sizeof(buf);
    ssize_t got;

    if (limit - total < want)
      want = limit - total;

    got = read(fd, buf, want);
    if (got < 0)
      die_perror("read");
    if (got == 0)
      break;

    for (ssize_t i = 0; i < got; i++)
      checksum = (checksum * 257u) ^ (unsigned char)buf[i];

    total += (size_t)got;
  }

  if (close(fd) != 0)
    die_perror("close");

  return checksum ^ total;
}

int main(void) {
  char exe[4096];
  unsigned char random_bytes[24];
  struct sigaction ign = {0};
  struct sigaction old_pipe = {0};
  struct sigaction old_xfsz = {0};
  struct rlimit stack_limit;
  void *map;
  size_t dir_entries;
  uint64_t checksum;
  ssize_t exe_len;

  if (!setlocale(LC_ALL, "C.UTF-8") && !setlocale(LC_ALL, "C"))
    die_perror("setlocale");

  if (getrandom(random_bytes, sizeof(random_bytes), GRND_NONBLOCK) !=
      (ssize_t)sizeof(random_bytes))
    die_perror("getrandom");

  exe_len = readlink("/proc/self/exe", exe, sizeof(exe) - 1);
  if (exe_len < 0)
    die_perror("readlink /proc/self/exe");
  exe[exe_len] = '\0';

  require_path("/usr/bin/python3");
  require_path("/usr/lib/python3.12");
  require_path("/usr/lib/python3.12/encodings");
  require_path("/usr/lib/python3.12/encodings/__init__.py");

  dir_entries = scan_dir("/usr/lib/python3.12");
  checksum =
      read_file_checksum("/usr/lib/python3.12/encodings/__init__.py", 8192);

  ign.sa_handler = SIG_IGN;
  sigemptyset(&ign.sa_mask);
  ign.sa_flags = 0;

  // if (sigaction(SIGPIPE, &ign, &old_pipe) != 0)
  //   die_perror("sigaction SIGPIPE");
  // if (sigaction(SIGXFSZ, &ign, &old_xfsz) != 0)
  //   die_perror("sigaction SIGXFSZ");

  if (getrlimit(RLIMIT_STACK, &stack_limit) != 0)
    die_perror("getrlimit RLIMIT_STACK");

  map = mmap(NULL, 16384, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS,
             -1, 0);
  if (map == MAP_FAILED)
    die_perror("mmap");

  memset(map, 0x5a, 16384);

  if (mprotect(map, 4096, PROT_READ) != 0)
    die_perror("mprotect");

  if (((unsigned char *)map)[4096] != 0x5a)
    die_perror("mprotect verification");

  if (munmap(map, 16384) != 0)
    die_perror("munmap");

  printf("python_init_like_smoke ok exe=%s rand0=%u entries=%zu checksum=%llu "
         "stack=%llu\n",
         exe, (unsigned)random_bytes[0], dir_entries,
         (unsigned long long)checksum,
         (unsigned long long)stack_limit.rlim_cur);
  return 0;
}
