/*
 * Tries to trigger passive CPU migration without explicitly changing
 * affinity. The process remains migratable across all online CPUs and
 * periodically yields so the scheduler can move it.
 */

#define _GNU_SOURCE

#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

static void allow_all_cpus(void) {
  cpu_set_t set;
  long nr_cpus = sysconf(_SC_NPROCESSORS_ONLN);

  if (nr_cpus <= 0)
    nr_cpus = 1;

  CPU_ZERO(&set);
  for (int cpu = 0; cpu < nr_cpus; cpu++)
    CPU_SET(cpu, &set);

  if (sched_setaffinity(0, sizeof(set), &set) != 0) {
    perror("sched_setaffinity");
    exit(1);
  }
}

int main(int argc, char *argv[]) {
  const uint64_t spin_iters =
      argc > 1 ? strtoull(argv[1], NULL, 0) : 50000000ULL;
  uint64_t rounds = 0;
  volatile uint64_t acc = 0;
  int last_cpu;
  struct timespec ts = {
      .tv_sec = 0,
      .tv_nsec = 1000000,
  };

  allow_all_cpus();

  last_cpu = sched_getcpu();
  if (last_cpu < 0) {
    perror("sched_getcpu");
    return 1;
  }

  printf("pid=%d start_cpu=%d spin_iters=%llu\n", getpid(), last_cpu,
         (unsigned long long)spin_iters);
  fflush(stdout);

  for (;;) {
    for (uint64_t i = 0; i < spin_iters; i++)
      acc += i ^ rounds;

    sched_yield();
    nanosleep(&ts, NULL);

    int cpu = sched_getcpu();
    if (cpu < 0) {
      perror("sched_getcpu");
      return 1;
    }

    if (cpu != last_cpu) {
      printf("passive migration round=%llu from=%d to=%d acc=%llu\n",
             (unsigned long long)rounds, last_cpu, cpu,
             (unsigned long long)acc);
      fflush(stdout);
      last_cpu = cpu;
    } else if ((rounds & 0x3f) == 0) {
      printf("still on cpu=%d round=%llu acc=%llu\n", cpu,
             (unsigned long long)rounds, (unsigned long long)acc);
      fflush(stdout);
    }

    rounds++;
  }
}
