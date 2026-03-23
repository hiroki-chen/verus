/*
 * Small TLS smoke test.
 *
 * This exercises ELF TLS storage plus a pthread-created thread so we can
 * distinguish basic dynamic loading from TLS/runtime initialization issues.
 */

#define _GNU_SOURCE

#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static __thread uint64_t tls_counter = 0;

struct thread_result {
  uint64_t main_before;
  uint64_t thread_seen;
  uint64_t thread_after;
};

static void *thread_main(void *arg) {
  struct thread_result *res = (struct thread_result *)arg;

  res->thread_seen = tls_counter;
  tls_counter = 0x2222222222222222ULL;
  res->thread_after = tls_counter;
  return NULL;
}

int main(void) {
  pthread_t thread;
  struct thread_result res = {0};

  tls_counter = 0x1111111111111111ULL;
  res.main_before = tls_counter;

  if (pthread_create(&thread, NULL, thread_main, &res) != 0) {
    perror("pthread_create");
    return 1;
  }

  if (pthread_join(thread, NULL) != 0) {
    perror("pthread_join");
    return 1;
  }

  if (res.main_before != 0x1111111111111111ULL) {
    fprintf(stderr, "tls_smoke: bad main_before=0x%llx\n",
            (unsigned long long)res.main_before);
    return 1;
  }

  if (res.thread_seen != 0) {
    fprintf(stderr, "tls_smoke: bad thread_seen=0x%llx\n",
            (unsigned long long)res.thread_seen);
    return 1;
  }

  if (res.thread_after != 0x2222222222222222ULL) {
    fprintf(stderr, "tls_smoke: bad thread_after=0x%llx\n",
            (unsigned long long)res.thread_after);
    return 1;
  }

  if (tls_counter != 0x1111111111111111ULL) {
    fprintf(stderr, "tls_smoke: main TLS corrupted=0x%llx\n",
            (unsigned long long)tls_counter);
    return 1;
  }

  printf("tls_smoke ok main=0x%llx thread=0x%llx\n",
         (unsigned long long)tls_counter,
         (unsigned long long)res.thread_after);
  return 0;
}
