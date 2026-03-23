#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

static void stage(const char *name) {
  fprintf(stderr, "read_localtime_file_smoke stage=%s\n", name);
  fflush(stderr);
}

static unsigned long hash_bytes(const unsigned char *buf, size_t len) {
  unsigned long h = 1469598103934665603UL;
  for (size_t i = 0; i < len; ++i) {
    h ^= (unsigned long)buf[i];
    h *= 1099511628211UL;
  }
  return h;
}

int main(void) {
  const char *path = "/etc/localtime";
  struct stat st;
  unsigned char *buf = NULL;
  ssize_t got;
  int fd;
  unsigned long h;

  memset(&st, 0, sizeof(st));

  stage("openat");
  fd = openat(AT_FDCWD, path, O_RDONLY | O_CLOEXEC);
  if (fd < 0) {
    perror("openat");
    return 1;
  }

  stage("fstat");
  if (fstat(fd, &st) != 0) {
    perror("fstat");
    close(fd);
    return 1;
  }

  if (st.st_size <= 0 || st.st_size > (1 << 20)) {
    fprintf(stderr, "unexpected /etc/localtime size=%lld\n", (long long)st.st_size);
    close(fd);
    return 1;
  }

  stage("malloc");
  buf = (unsigned char *)malloc((size_t)st.st_size);
  if (buf == NULL) {
    perror("malloc");
    close(fd);
    return 1;
  }

  stage("read");
  got = read(fd, buf, (size_t)st.st_size);
  if (got < 0) {
    perror("read");
    free(buf);
    close(fd);
    return 1;
  }

  if (got != st.st_size) {
    fprintf(stderr, "short read expected=%lld got=%lld\n",
            (long long)st.st_size, (long long)got);
    free(buf);
    close(fd);
    return 1;
  }

  stage("close");
  if (close(fd) != 0) {
    perror("close");
    free(buf);
    return 1;
  }

  h = hash_bytes(buf, (size_t)got);
  printf("read_localtime_file_smoke ok size=%lld hash=%lu first4=%02x%02x%02x%02x\n",
         (long long)got, h,
         got > 0 ? buf[0] : 0, got > 1 ? buf[1] : 0,
         got > 2 ? buf[2] : 0, got > 3 ? buf[3] : 0);

  free(buf);
  return 0;
}
