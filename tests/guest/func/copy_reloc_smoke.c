#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern char **environ;

static unsigned long hash_bytes(const unsigned char *buf, size_t len) {
  unsigned long h = 1469598103934665603UL;
  for (size_t i = 0; i < len; ++i) {
    h ^= (unsigned long)buf[i];
    h *= 1099511628211UL;
  }
  return h;
}

int main(void) {
  const char *banner = "copy_reloc_smoke";
  char env_buf[512];
  size_t env_len = 0;
  unsigned long env_hash = 0;
  unsigned long io_hash = 0;

  memset(env_buf, 0, sizeof(env_buf));

  if (stdout == NULL || stderr == NULL || stdin == NULL) {
    fprintf(stderr, "copy reloc stdio pointers are null\n");
    return 1;
  }

  if (setenv("COPY_RELOC_SMOKE", "enabled", 1) != 0) {
    perror("setenv");
    return 1;
  }

  if (getenv("COPY_RELOC_SMOKE") == NULL) {
    fprintf(stderr, "getenv failed after setenv\n");
    return 1;
  }

  for (char **p = environ; p != NULL && *p != NULL; ++p) {
    size_t len = strlen(*p);
    if (env_len + len + 1 >= sizeof(env_buf))
      break;
    memcpy(env_buf + env_len, *p, len);
    env_len += len;
    env_buf[env_len++] = '\n';
  }

  env_hash = hash_bytes((const unsigned char *)env_buf, env_len);

  if (fprintf(stdout, "%s stdout-ok\n", banner) < 0) {
    perror("fprintf(stdout)");
    return 1;
  }

  if (fprintf(stderr, "%s stderr-ok\n", banner) < 0) {
    perror("fprintf(stderr)");
    return 1;
  }

  if (fflush(stdout) != 0 || fflush(stderr) != 0) {
    perror("fflush");
    return 1;
  }

  io_hash ^= (unsigned long)(uintptr_t)stdin;
  io_hash ^= (unsigned long)(uintptr_t)stdout;
  io_hash ^= (unsigned long)(uintptr_t)stderr;
  io_hash ^= (unsigned long)(uintptr_t)environ;
  io_hash ^= (unsigned long)getpid();
  io_hash ^= (unsigned long)errno;

  printf("copy_reloc_smoke ok env_hash=%lu io_hash=%lu env_count=%zu\n",
         env_hash, io_hash, env_len);
  return 0;
}
