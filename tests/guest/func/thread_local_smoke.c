/*
 * Minimal thread-local storage smoke test.
 *
 * This stays in a single thread and only exercises ELF TLS access so we can
 * separate plain TLS issues from pthread/signal-registration issues.
 */

#define _GNU_SOURCE

#include <stdint.h>
#include <stdio.h>

static __thread uint64_t tls_word = 0;

int main(void) {
  tls_word = 0x123456789abcdef0ULL;
  if (tls_word != 0x123456789abcdef0ULL) {
    fprintf(stderr, "thread_local_smoke: first readback mismatch 0x%llx\n",
            (unsigned long long)tls_word);
    return 1;
  }

  tls_word ^= 0xffff0000ffff0000ULL;
  if (tls_word != 0xedcb56786543def0ULL) {
    fprintf(stderr, "thread_local_smoke: second readback mismatch 0x%llx\n",
            (unsigned long long)tls_word);
    return 1;
  }

  printf("thread_local_smoke ok tls=0x%llx\n",
         (unsigned long long)tls_word);
  return 0;
}
