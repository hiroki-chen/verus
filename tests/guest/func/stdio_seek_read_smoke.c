#include <errno.h>
#include <fcntl.h>
#include <stdio_ext.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

struct tzhead_raw {
  unsigned char bytes[44];
};

static void stage(const char *name) {
  fprintf(stderr, "stdio_seek_read_smoke stage=%s\n", name);
  fflush(stderr);
}

static uint32_t decode_be32(const unsigned char *p) {
  return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) |
         ((uint32_t)p[2] << 8) | (uint32_t)p[3];
}

static int compute_second_header_skip(const unsigned char *hdr, off_t *skip_out) {
  uint32_t timecnt;
  uint32_t typecnt;
  uint32_t charcnt;
  uint32_t leapcnt;
  uint32_t isstdcnt;
  uint32_t isgmtcnt;
  off_t skip;

  if (memcmp(hdr, "TZif", 4) != 0) {
    fprintf(stderr, "bad tzfile magic\n");
    return -1;
  }

  if (hdr[4] == '\0') {
    fprintf(stderr, "tzfile has no second header\n");
    return -1;
  }

  timecnt = decode_be32(hdr + 32);
  typecnt = decode_be32(hdr + 36);
  charcnt = decode_be32(hdr + 40);
  leapcnt = decode_be32(hdr + 28);
  isstdcnt = decode_be32(hdr + 24);
  isgmtcnt = decode_be32(hdr + 20);

  skip = (off_t)timecnt * (4 + 1) + (off_t)typecnt * 6 + (off_t)charcnt +
         (off_t)leapcnt * 8 + (off_t)isstdcnt + (off_t)isgmtcnt;
  *skip_out = skip;
  return 0;
}

static unsigned long hash_bytes(const unsigned char *buf, size_t len) {
  unsigned long h = 1469598103934665603UL;
  for (size_t i = 0; i < len; ++i) {
    h ^= (unsigned long)buf[i];
    h *= 1099511628211UL;
  }
  return h;
}

static int do_stdio_path(const char *path, unsigned long *out_hash) {
  FILE *f = fopen(path, "r");
  struct tzhead_raw hdr1;
  struct tzhead_raw hdr2;
  struct stat st;
  size_t n1, n2;
  off_t skip;

  if (f == NULL) {
    perror("fopen");
    return -1;
  }

  if (fstat(fileno(f), &st) != 0) {
    perror("fstat");
    fclose(f);
    return -1;
  }

  stage("stdio-fread-1");
  n1 = fread(&hdr1, 1, sizeof(hdr1), f);
  if (n1 != sizeof(hdr1)) {
    fprintf(stderr, "stdio short first read got=%zu\n", n1);
    fclose(f);
    return -1;
  }

  if (compute_second_header_skip(hdr1.bytes, &skip) != 0) {
    fclose(f);
    return -1;
  }
  stage("stdio-fseek");
  if (fseek(f, skip, SEEK_CUR) != 0) {
    perror("fseek");
    fclose(f);
    return -1;
  }

  stage("stdio-fread-2");
  n2 = fread(&hdr2, 1, sizeof(hdr2), f);
  if (n2 != sizeof(hdr2)) {
    fprintf(stderr, "stdio short second read got=%zu\n", n2);
    fclose(f);
    return -1;
  }

  fclose(f);
  *out_hash = hash_bytes(hdr1.bytes, sizeof(hdr1.bytes)) ^
              (hash_bytes(hdr2.bytes, sizeof(hdr2.bytes)) << 1);
  return 0;
}

static int do_stdio_unlocked_path(const char *path, unsigned long *out_hash) {
  FILE *f = fopen(path, "rce");
  struct tzhead_raw hdr1;
  struct tzhead_raw hdr2;
  struct stat st;
  size_t n1, n2;
  off_t skip;

  if (f == NULL) {
    perror("fopen-rce");
    return -1;
  }

  if (fstat(fileno(f), &st) != 0) {
    perror("fstat-unlocked");
    fclose(f);
    return -1;
  }

  __fsetlocking(f, FSETLOCKING_BYCALLER);

  stage("stdio-unlocked-fread-1");
  n1 = fread_unlocked(&hdr1, 1, sizeof(hdr1), f);
  if (n1 != sizeof(hdr1)) {
    fprintf(stderr, "stdio unlocked short first read got=%zu\n", n1);
    fclose(f);
    return -1;
  }

  if (compute_second_header_skip(hdr1.bytes, &skip) != 0) {
    fclose(f);
    return -1;
  }
  stage("stdio-unlocked-fseek");
  if (fseek(f, skip, SEEK_CUR) != 0) {
    perror("fseek-unlocked");
    fclose(f);
    return -1;
  }

  stage("stdio-unlocked-fread-2");
  n2 = fread_unlocked(&hdr2, 1, sizeof(hdr2), f);
  if (n2 != sizeof(hdr2)) {
    fprintf(stderr, "stdio unlocked short second read got=%zu\n", n2);
    fclose(f);
    return -1;
  }

  fclose(f);
  *out_hash = hash_bytes(hdr1.bytes, sizeof(hdr1.bytes)) ^
              (hash_bytes(hdr2.bytes, sizeof(hdr2.bytes)) << 1);
  return 0;
}

static int do_fd_path(const char *path, unsigned long *out_hash) {
  int fd = open(path, O_RDONLY | O_CLOEXEC);
  struct tzhead_raw hdr1;
  struct tzhead_raw hdr2;
  ssize_t n1, n2;
  off_t skip;

  if (fd < 0) {
    perror("open");
    return -1;
  }

  stage("fd-read-1");
  n1 = read(fd, &hdr1, sizeof(hdr1));
  if (n1 != (ssize_t)sizeof(hdr1)) {
    fprintf(stderr, "fd short first read got=%zd errno=%d\n", n1, errno);
    close(fd);
    return -1;
  }

  if (compute_second_header_skip(hdr1.bytes, &skip) != 0) {
    close(fd);
    return -1;
  }
  stage("fd-lseek");
  if (lseek(fd, skip, SEEK_CUR) < 0) {
    perror("lseek");
    close(fd);
    return -1;
  }

  stage("fd-read-2");
  n2 = read(fd, &hdr2, sizeof(hdr2));
  if (n2 != (ssize_t)sizeof(hdr2)) {
    fprintf(stderr, "fd short second read got=%zd errno=%d\n", n2, errno);
    close(fd);
    return -1;
  }

  close(fd);
  *out_hash = hash_bytes(hdr1.bytes, sizeof(hdr1.bytes)) ^
              (hash_bytes(hdr2.bytes, sizeof(hdr2.bytes)) << 1);
  return 0;
}

int main(int argc, char **argv) {
  const char *path = "/etc/localtime";
  unsigned long stdio_hash = 0;
  unsigned long stdio_unlocked_hash = 0;
  unsigned long fd_hash = 0;
  int stdio_ok = 0;
  int stdio_unlocked_ok = 0;
  int fd_ok = 0;
  const char *mode = argc > 1 ? argv[1] : "all";

  if (strcmp(mode, "all") == 0 || strcmp(mode, "stdio") == 0) {
    stage("stdio-path");
    if (do_stdio_path(path, &stdio_hash) != 0) {
      fprintf(stderr, "stdio path failed\n");
    } else {
      stdio_ok = 1;
    }
  }

  if (strcmp(mode, "all") == 0 || strcmp(mode, "stdio_unlocked") == 0) {
    stage("stdio-unlocked-path");
    if (do_stdio_unlocked_path(path, &stdio_unlocked_hash) != 0) {
      fprintf(stderr, "stdio unlocked path failed\n");
    } else {
      stdio_unlocked_ok = 1;
    }
  }

  if (strcmp(mode, "all") == 0 || strcmp(mode, "fd") == 0) {
    stage("fd-path");
    if (do_fd_path(path, &fd_hash) != 0) {
      fprintf(stderr, "fd path failed\n");
    } else {
      fd_ok = 1;
    }
  }

  if (strcmp(mode, "stdio") == 0) {
    printf("stdio_seek_read_smoke mode=stdio ok=%d hash=%lu\n", stdio_ok, stdio_hash);
    return stdio_ok ? 0 : 1;
  }

  if (strcmp(mode, "stdio_unlocked") == 0) {
    printf("stdio_seek_read_smoke mode=stdio_unlocked ok=%d hash=%lu\n",
           stdio_unlocked_ok, stdio_unlocked_hash);
    return stdio_unlocked_ok ? 0 : 1;
  }

  if (strcmp(mode, "fd") == 0) {
    printf("stdio_seek_read_smoke mode=fd ok=%d hash=%lu\n", fd_ok, fd_hash);
    return fd_ok ? 0 : 1;
  }

  printf("stdio_seek_read_smoke stdio_ok=%d stdio_unlocked_ok=%d fd_ok=%d stdio_hash=%lu stdio_unlocked_hash=%lu fd_hash=%lu stdio_match=%s unlocked_match=%s\n",
         stdio_ok, stdio_unlocked_ok, fd_ok,
         stdio_hash, stdio_unlocked_hash, fd_hash,
         stdio_hash == fd_hash ? "yes" : "no",
         stdio_unlocked_hash == fd_hash ? "yes" : "no");
  return (stdio_ok && stdio_unlocked_ok && fd_ok) ? 0 : 1;
}
