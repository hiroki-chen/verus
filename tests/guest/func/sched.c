/*
 * Tests if we can support CPU affinity in the guest.
 *
 * This is important for testing task migration and CPU hotplug.
 */

#define _GNU_SOURCE

#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

static void pin_cpu(int cpu) {
  cpu_set_t set;
  CPU_ZERO(&set);
  CPU_SET(cpu, &set);
  if (sched_setaffinity(0, sizeof(set), &set) != 0) {
    perror("sched_setaffinity");
    exit(1);
  }

  printf("Pinned to %d\n", cpu);
  fflush(stdout);
}

int main(int argc, char *argv[]) {
  int a = argc > 1 ? atoi(argv[1]) : 0;
  int b = argc > 2 ? atoi(argv[2]) : 1;
  volatile uint64_t x = 0;

  printf("pid=%d cpu_a=%d cpu_b=%d\n", getpid(), a, b);
  fflush(stdout);
  for (;;) {
    pin_cpu(a);
    for (uint64_t i = 0; i < 100000000ULL; i++)
      x += i;
    pin_cpu(b);
    for (uint64_t i = 0; i < 100000000ULL; i++)
      x += i;

    printf("x => %ld\n", x);
  }
}
