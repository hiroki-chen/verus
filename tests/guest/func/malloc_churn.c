/*
 * Heap churn test that repeatedly allocates, touches, resizes, and frees
 * blocks of varying sizes to exercise both brk- and mmap-backed allocations.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#define SLOT_COUNT 256

struct slot {
  uint8_t *ptr;
  size_t len;
  uint8_t tag;
};

static uint64_t xorshift64(uint64_t *state) {
  uint64_t x = *state;

  x ^= x << 13;
  x ^= x >> 7;
  x ^= x << 17;
  *state = x;
  return x;
}

static size_t pick_size(uint64_t value) {
  switch (value & 3u) {
  case 0:
    return 64 + (value % 4096);
  case 1:
    return 4096 + (value % (128 * 1024));
  case 2:
    return 128 * 1024 + (value % (2 * 1024 * 1024));
  default:
    return 2 * 1024 * 1024 + (value % (8 * 1024 * 1024));
  }
}

static uint8_t block_value(uint8_t tag, size_t idx) {
  return (uint8_t)(tag ^ (uint8_t)idx);
}

static void fill_block(uint8_t *ptr, size_t start, size_t len, uint8_t tag) {
  for (size_t i = 0; i < len; i++)
    ptr[i] = block_value(tag, start + i);
}

static void verify_block(const struct slot *slot, const char *label) {
  for (size_t i = 0; i < slot->len; i++) {
    uint8_t expected = block_value(slot->tag, i);
    if (slot->ptr[i] != expected) {
      fprintf(stderr,
              "%s mismatch len=%zu index=%zu expected=0x%02x got=0x%02x\n",
              label, slot->len, i, expected, slot->ptr[i]);
      exit(1);
    }
  }
}

int main(int argc, char *argv[]) {
  struct slot slots[SLOT_COUNT] = {0};
  const uint64_t rounds =
      argc > 1 ? strtoull(argv[1], NULL, 0) : 20000ULL;
  uint64_t seed = argc > 2 ? strtoull(argv[2], NULL, 0)
                           : ((uint64_t)time(NULL) << 32) ^ (uint64_t)getpid();
  uint64_t total_bytes = 0;

  if (seed == 0)
    seed = 1;

  printf("malloc_churn rounds=%llu seed=%llu slots=%u\n",
         (unsigned long long)rounds, (unsigned long long)seed, SLOT_COUNT);
  fflush(stdout);

  for (uint64_t round = 0; round < rounds; round++) {
    struct slot *slot;
    uint64_t v = xorshift64(&seed);
    size_t idx = (size_t)(v % SLOT_COUNT);
    size_t len;

    slot = &slots[idx];

    if (slot->ptr && ((v >> 8) & 1u)) {
      verify_block(slot, "free");
      free(slot->ptr);
      total_bytes -= slot->len;
      slot->ptr = NULL;
      slot->len = 0;
      slot->tag = 0;
    }

    v = xorshift64(&seed);
    len = pick_size(v);

    if (!slot->ptr) {
      slot->ptr = malloc(len);
      if (!slot->ptr) {
        perror("malloc");
        return 1;
      }
      slot->len = len;
      slot->tag = (uint8_t)(v >> 16);
      fill_block(slot->ptr, 0, slot->len, slot->tag);
      total_bytes += slot->len;
    } else {
      size_t old_len = slot->len;
      uint8_t old_tag = slot->tag;
      uint8_t *new_ptr;

      verify_block(slot, "realloc-before");
      new_ptr = realloc(slot->ptr, len);
      if (!new_ptr) {
        perror("realloc");
        return 1;
      }

      slot->ptr = new_ptr;
      slot->len = len;
      slot->tag = (uint8_t)(v >> 24);

      for (size_t i = 0; i < (old_len < len ? old_len : len); i++) {
        uint8_t expected = block_value(old_tag, i);
        if (slot->ptr[i] != expected) {
          fprintf(stderr, "realloc-preserve mismatch index=%zu\n", i);
          return 1;
        }
      }

      if (len > old_len)
        fill_block(slot->ptr + old_len, old_len, len - old_len, slot->tag);
      fill_block(slot->ptr, 0, old_len < len ? old_len : len, slot->tag);
      total_bytes = total_bytes - old_len + len;
    }

    if ((round & 0xffu) == 0) {
      printf("malloc_churn round=%llu live_bytes=%llu sample_idx=%zu len=%zu\n",
             (unsigned long long)round, (unsigned long long)total_bytes, idx,
             slot->len);
      fflush(stdout);
    }
  }

  for (size_t i = 0; i < SLOT_COUNT; i++) {
    if (!slots[i].ptr)
      continue;
    verify_block(&slots[i], "final");
    free(slots[i].ptr);
  }

  printf("malloc_churn ok rounds=%llu\n", (unsigned long long)rounds);
  return 0;
}
