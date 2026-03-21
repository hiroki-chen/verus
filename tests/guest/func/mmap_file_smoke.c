/*
 * Memory-mapped file smoke test that exercises mkstemp, ftruncate, mmap,
 * mprotect, msync, pread, and munmap on a multi-page file.
 */

#define _GNU_SOURCE

#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <unistd.h>

static void die_perror(const char *what) {
  perror(what);
  exit(1);
}

static uint8_t pattern_byte(size_t index) {
  return (uint8_t)(((index * 29u) ^ (index >> 3) ^ 0x5au) & 0xffu);
}

int main(void) {
  char path[] = "/tmp/mmap-file-smoke.XXXXXX";
  const size_t length = 2 * 1024 * 1024;
  const size_t sample_count = 4096;
  uint8_t verify[4096];
  uint8_t *map;
  int fd;
  uint64_t checksum = 0;

  fd = mkstemp(path);
  if (fd < 0)
    die_perror("mkstemp");

  if (unlink(path) != 0)
    die_perror("unlink temp path");

  if (ftruncate(fd, (off_t)length) != 0)
    die_perror("ftruncate");

  map = mmap(NULL, length, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  if (map == MAP_FAILED)
    die_perror("mmap");

  for (size_t i = 0; i < length; i++)
    map[i] = pattern_byte(i);

  if (msync(map, length, MS_SYNC) != 0)
    die_perror("msync");

  if (mprotect(map, length, PROT_READ) != 0)
    die_perror("mprotect");

  for (size_t i = 0; i < sample_count; i++) {
    size_t index = (i * 509u) % length;
    uint8_t expected = pattern_byte(index);
    if (map[index] != expected) {
      fprintf(stderr,
              "mmap_file_smoke: mmap verify mismatch at %zu expected=0x%02x "
              "got=0x%02x\n",
              index, expected, map[index]);
      return 1;
    }
    checksum = (checksum * 257u) ^ map[index];
  }

  if (pread(fd, verify, sizeof(verify), (off_t)(length / 3)) !=
      (ssize_t)sizeof(verify))
    die_perror("pread");

  for (size_t i = 0; i < sizeof(verify); i++) {
    size_t index = (length / 3) + i;
    uint8_t expected = pattern_byte(index);
    if (verify[i] != expected) {
      fprintf(stderr,
              "mmap_file_smoke: pread verify mismatch at %zu expected=0x%02x "
              "got=0x%02x\n",
              index, expected, verify[i]);
      return 1;
    }
  }

  if (munmap(map, length) != 0)
    die_perror("munmap");
  if (close(fd) != 0)
    die_perror("close");

  printf("mmap_file_smoke ok bytes=%zu checksum=%llu samples=%zu\n", length,
         (unsigned long long)checksum, sample_count);
  return 0;
}
