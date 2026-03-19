/*
 * Basic heap test that exercises malloc/calloc/realloc/free and verifies
 * the contents survive common resize and copy patterns.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void fill_pattern(uint8_t *buf, size_t len, uint8_t seed) {
  for (size_t i = 0; i < len; i++)
    buf[i] = (uint8_t)(seed + (uint8_t)i);
}

static void check_pattern(const uint8_t *buf, size_t len, uint8_t seed,
                          const char *label) {
  for (size_t i = 0; i < len; i++) {
    uint8_t expected = (uint8_t)(seed + (uint8_t)i);
    if (buf[i] != expected) {
      fprintf(stderr,
              "%s mismatch at index=%zu expected=0x%02x got=0x%02x\n",
              label, i, expected, buf[i]);
      exit(1);
    }
  }
}

int main(void) {
  const size_t small = 4096;
  const size_t medium = 128 * 1024;
  const size_t large = 2 * 1024 * 1024;
  uint8_t *a = malloc(small);
  uint8_t *b = calloc(medium, 1);
  uint8_t *c;

  if (!a || !b) {
    perror("malloc/calloc");
    return 1;
  }

  fill_pattern(a, small, 0x11);
  check_pattern(a, small, 0x11, "malloc");

  for (size_t i = 0; i < medium; i++) {
    if (b[i] != 0) {
      fprintf(stderr, "calloc returned non-zero byte at index=%zu\n", i);
      return 1;
    }
  }

  memset(b, 0x5a, medium);
  c = realloc(b, large);
  if (!c) {
    perror("realloc-grow");
    free(a);
    free(b);
    return 1;
  }

  for (size_t i = 0; i < medium; i++) {
    if (c[i] != 0x5a) {
      fprintf(stderr, "realloc-grow corrupted byte at index=%zu\n", i);
      free(a);
      free(c);
      return 1;
    }
  }

  memset(c + medium, 0xa5, large - medium);
  c = realloc(c, medium / 2);
  if (!c) {
    perror("realloc-shrink");
    free(a);
    return 1;
  }

  for (size_t i = 0; i < medium / 2; i++) {
    if (c[i] != 0x5a) {
      fprintf(stderr, "realloc-shrink corrupted byte at index=%zu\n", i);
      free(a);
      free(c);
      return 1;
    }
  }

  check_pattern(a, small, 0x11, "malloc-after-realloc");

  printf("malloc_basic ok small=%zu medium=%zu large=%zu\n", small, medium,
         large);

  free(a);
  free(c);
  return 0;
}
