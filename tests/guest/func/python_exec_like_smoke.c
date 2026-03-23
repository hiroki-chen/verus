#define _GNU_SOURCE

#include <errno.h>
#include <expat.h>
#include <locale.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/random.h>
#include <sys/resource.h>
#include <unistd.h>
#include <zlib.h>

extern char **environ;

__thread uint64_t tls_cookie = 0x1122334455667788ULL;

static unsigned char runtime_blob[256 * 1024];
static uint64_t runtime_words[4096];
static char runtime_banner[512];

static void fatal(const char *what) {
  perror(what);
  exit(1);
}

static void fill_runtime_blob(void) {
  for (size_t i = 0; i < sizeof(runtime_blob); ++i)
    runtime_blob[i] = (unsigned char)((i * 37u + 11u) & 0xffu);

  for (size_t i = 0; i < sizeof(runtime_words) / sizeof(runtime_words[0]); ++i)
    runtime_words[i] = 0x9e3779b97f4a7c15ULL ^ (uint64_t)i;

  snprintf(runtime_banner, sizeof(runtime_banner),
           "python_exec_like_smoke pid=%ld stdin=%p stdout=%p stderr=%p",
           (long)getpid(), (void *)stdin, (void *)stdout, (void *)stderr);
}

static uint64_t touch_runtime_blob(void) {
  uint64_t acc = 0;

  for (size_t i = 0; i < sizeof(runtime_blob); i += 64)
    acc = (acc << 5) ^ (acc >> 2) ^ runtime_blob[i];

  for (size_t i = 0; i < sizeof(runtime_words) / sizeof(runtime_words[0]); ++i)
    acc ^= runtime_words[i] + (uint64_t)i * 17ULL;

  acc ^= (uint64_t)runtime_banner[0];
  acc ^= tls_cookie;
  return acc;
}

static void parse_small_xml(void) {
  static const char xml[] =
      "<root><item key='alpha'>1</item><item key='beta'>2</item></root>";
  XML_Parser parser = XML_ParserCreate(NULL);

  if (!parser) {
    fprintf(stderr, "XML_ParserCreate failed\n");
    exit(1);
  }

  if (XML_Parse(parser, xml, (int)strlen(xml), XML_TRUE) == XML_STATUS_ERROR) {
    fprintf(stderr, "XML_Parse failed at line %lu\n",
            XML_GetCurrentLineNumber(parser));
    XML_ParserFree(parser);
    exit(1);
  }

  XML_ParserFree(parser);
}

static uint64_t compress_runtime_blob(void) {
  uLongf dst_len = compressBound(sizeof(runtime_blob));
  Bytef *dst = malloc(dst_len);
  uint64_t digest = 0;

  if (!dst) {
    fprintf(stderr, "malloc failed\n");
    exit(1);
  }

  if (compress2(dst, &dst_len, runtime_blob, sizeof(runtime_blob),
                Z_BEST_SPEED) != Z_OK) {
    fprintf(stderr, "compress2 failed\n");
    free(dst);
    exit(1);
  }

  for (uLongf i = 0; i < dst_len; i += 97)
    digest = (digest * 1315423911u) ^ dst[i];

  free(dst);
  return digest ^ dst_len;
}

static void exercise_mapping(void) {
  const size_t len = 4 * 4096;
  unsigned char *map =
      mmap(NULL, len, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);

  if (map == MAP_FAILED)
    fatal("mmap");

  memset(map, 0x5a, len);

  if (mprotect(map, len, PROT_READ) != 0)
    fatal("mprotect");

  if (map[0] != 0x5a || map[len - 1] != 0x5a) {
    fprintf(stderr, "mprotect verification failed\n");
    munmap(map, len);
    exit(1);
  }

  if (munmap(map, len) != 0)
    fatal("munmap");
}

int main(void) {
  struct rlimit rl = {0};
  unsigned char rnd[16];
  const char *loc;
  uint64_t blob_acc;
  uint64_t z_digest;
  double trig;
  size_t env_count = 0;

  fill_runtime_blob();

  loc = setlocale(LC_ALL, "");
  if (!loc)
    fatal("setlocale");

  if (getrandom(rnd, sizeof(rnd), 0) != (ssize_t)sizeof(rnd))
    fatal("getrandom");

  if (getrlimit(RLIMIT_STACK, &rl) != 0)
    fatal("getrlimit");

  for (char **p = environ; p && *p; ++p)
    env_count++;

  parse_small_xml();
  blob_acc = touch_runtime_blob();
  z_digest = compress_runtime_blob();
  exercise_mapping();

  trig = cos(0.0) + sin(0.5) + sqrt(9.0);

  printf(
      "python_exec_like_smoke ok tls=0x%llx blob=0x%llx z=0x%llx trig=%.6f "
      "env=%zu stack=%llu rand0=%u banner=%s\n",
      (unsigned long long)tls_cookie, (unsigned long long)blob_acc,
      (unsigned long long)z_digest, trig, env_count,
      (unsigned long long)rl.rlim_cur, (unsigned)rnd[0], runtime_banner);

  return 0;
}
