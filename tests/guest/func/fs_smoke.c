/*
 * Filesystem smoke test that exercises mkdir, open, read/write, rename,
 * stat, opendir/readdir, and unlink/rmdir using a small directory tree.
 */

#define _GNU_SOURCE

#include <dirent.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

static void die_perror(const char *what) {
  perror(what);
  exit(1);
}

static void write_full(int fd, const void *buf, size_t len) {
  const uint8_t *p = (const uint8_t *)buf;

  while (len > 0) {
    ssize_t n = write(fd, p, len);
    if (n < 0)
      die_perror("write");
    p += (size_t)n;
    len -= (size_t)n;
  }
}

static void read_full(int fd, void *buf, size_t len) {
  uint8_t *p = (uint8_t *)buf;

  while (len > 0) {
    ssize_t n = read(fd, p, len);
    if (n < 0)
      die_perror("read");
    if (n == 0) {
      fprintf(stderr, "unexpected EOF\n");
      exit(1);
    }
    p += (size_t)n;
    len -= (size_t)n;
  }
}

static uint64_t checksum_bytes(const uint8_t *buf, size_t len) {
  uint64_t sum = 0;

  for (size_t i = 0; i < len; i++)
    sum = (sum * 131u) ^ buf[i];

  return sum;
}

static int is_dot_entry(const char *name) {
  return strcmp(name, ".") == 0 || strcmp(name, "..") == 0;
}

int main(void) {
  char root[] = "/tmp/fs-smoke.XXXXXX";
  char dir_a[256];
  char dir_b[256];
  char file_a[256];
  char file_b[256];
  char renamed[256];
  uint8_t payload[64 * 1024];
  uint8_t verify[64 * 1024];
  struct stat st;
  DIR *dir;
  struct dirent *ent;
  int fd;
  int entries = 0;
  uint64_t sum;

  if (!mkdtemp(root))
    die_perror("mkdtemp");

  snprintf(dir_a, sizeof(dir_a), "%s/input", root);
  snprintf(dir_b, sizeof(dir_b), "%s/output", root);
  snprintf(file_a, sizeof(file_a), "%s/input/data.bin", root);
  snprintf(file_b, sizeof(file_b), "%s/output/meta.txt", root);
  snprintf(renamed, sizeof(renamed), "%s/output/data-renamed.bin", root);

  if (mkdir(dir_a, 0755) != 0)
    die_perror("mkdir input");
  if (mkdir(dir_b, 0755) != 0)
    die_perror("mkdir output");

  for (size_t i = 0; i < sizeof(payload); i++)
    payload[i] = (uint8_t)((i * 17u + 23u) & 0xffu);

  fd = open(file_a, O_CREAT | O_TRUNC | O_WRONLY, 0644);
  if (fd < 0)
    die_perror("open write file_a");
  write_full(fd, payload, sizeof(payload));
  if (close(fd) != 0)
    die_perror("close file_a");

  if (rename(file_a, renamed) != 0)
    die_perror("rename");

  fd = open(renamed, O_RDONLY);
  if (fd < 0)
    die_perror("open read renamed");
  read_full(fd, verify, sizeof(verify));
  if (close(fd) != 0)
    die_perror("close renamed");

  if (memcmp(payload, verify, sizeof(payload)) != 0) {
    fprintf(stderr, "fs_smoke: payload mismatch after rename/read\n");
    return 1;
  }

  if (stat(renamed, &st) != 0)
    die_perror("stat renamed");
  if ((size_t)st.st_size != sizeof(payload)) {
    fprintf(stderr, "fs_smoke: unexpected file size %lld\n",
            (long long)st.st_size);
    return 1;
  }

  sum = checksum_bytes(verify, sizeof(verify));

  fd = open(file_b, O_CREAT | O_TRUNC | O_WRONLY, 0644);
  if (fd < 0)
    die_perror("open meta");
  dprintf(fd, "bytes=%zu checksum=%llu\n", sizeof(verify),
          (unsigned long long)sum);
  if (close(fd) != 0)
    die_perror("close meta");

  dir = opendir(root);
  if (!dir)
    die_perror("opendir root");
  while ((ent = readdir(dir)) != NULL) {
    if (is_dot_entry(ent->d_name))
      continue;
    entries++;
  }
  if (closedir(dir) != 0)
    die_perror("closedir root");

  if (entries != 2) {
    fprintf(stderr, "fs_smoke: expected 2 top-level entries, got %d\n", entries);
    return 1;
  }

  if (unlink(renamed) != 0)
    die_perror("unlink renamed");
  if (unlink(file_b) != 0)
    die_perror("unlink meta");
  if (rmdir(dir_a) != 0)
    die_perror("rmdir input");
  if (rmdir(dir_b) != 0)
    die_perror("rmdir output");
  if (rmdir(root) != 0)
    die_perror("rmdir root");

  printf("fs_smoke ok bytes=%zu checksum=%llu entries=%d\n", sizeof(payload),
         (unsigned long long)sum, entries);
  return 0;
}
