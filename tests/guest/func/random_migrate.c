/*
 * Actively requests random CPU migration by changing the task affinity
 * to one randomly chosen online CPU at a time.
 */

#define _GNU_SOURCE

#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

static uint64_t xorshift64(uint64_t *state) {
  uint64_t x = *state;

  x ^= x << 13;
  x ^= x >> 7;
  x ^= x << 17;
  *state = x;
  return x;
}

static void pin_cpu(int cpu) {
  cpu_set_t set;

  CPU_ZERO(&set);
  CPU_SET(cpu, &set);
  if (sched_setaffinity(0, sizeof(set), &set) != 0) {
    perror("sched_setaffinity");
    exit(1);
  }
}

static int syscall_getcpu_or_die(unsigned *cpu, unsigned *node) {
  long ret = syscall(SYS_getcpu, cpu, node, NULL);

  if (ret != 0) {
    perror("getcpu");
    exit(1);
  }

  return 0;
}

static void print_allowed_cpus(void) {
  cpu_set_t set;
  int first = 1;

  CPU_ZERO(&set);
  if (sched_getaffinity(0, sizeof(set), &set) != 0) {
    perror("sched_getaffinity");
    exit(1);
  }

  printf("allowed_cpus=");
  for (int cpu = 0; cpu < CPU_SETSIZE; cpu++) {
    if (!CPU_ISSET(cpu, &set))
      continue;
    printf("%s%d", first ? "" : ",", cpu);
    first = 0;
  }
  if (first)
    printf("<empty>");
  printf("\n");
}

int main(int argc, char *argv[]) {
  long nr_cpus = sysconf(_SC_NPROCESSORS_ONLN);
  uint64_t seed;
  uint64_t rounds = 0;
  const uint64_t spin_iters =
      argc > 1 ? strtoull(argv[1], NULL, 0) : 20000000ULL;
  volatile uint64_t acc = 0;

  if (nr_cpus <= 0)
    nr_cpus = 1;

  seed = argc > 2 ? strtoull(argv[2], NULL, 0)
                  : ((uint64_t)time(NULL) << 32) ^ (uint64_t)getpid();
  if (seed == 0)
    seed = 1;

  printf("pid=%d cpus=%ld seed=%llu spin_iters=%llu\n", getpid(), nr_cpus,
         (unsigned long long)seed, (unsigned long long)spin_iters);
  print_allowed_cpus();
  fflush(stdout);

  for (;;) {
    unsigned before_sys = 0, before_node = 0;
    unsigned after_sys = 0, after_node = 0;
    int target = (int)(xorshift64(&seed) % (uint64_t)nr_cpus);
    int before = sched_getcpu();
    if (before < 0) {
      perror("sched_getcpu");
      return 1;
    }
    syscall_getcpu_or_die(&before_sys, &before_node);

    pin_cpu(target);

    for (uint64_t i = 0; i < spin_iters; i++)
      acc += (uint64_t)target + i;

    int after = sched_getcpu();
    if (after < 0) {
      perror("sched_getcpu");
      return 1;
    }
    syscall_getcpu_or_die(&after_sys, &after_node);

    printf(
        "active migration round=%llu before_sched=%d before_sys=%u "
        "target=%d after_sched=%d after_sys=%u node=%u acc=%llu\n",
           (unsigned long long)rounds, before, before_sys, target, after,
           after_sys, after_node,
           (unsigned long long)acc);
    fflush(stdout);
    rounds++;
  }
}
