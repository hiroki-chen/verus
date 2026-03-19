/*
 * Simple smoke test for guest userspace execution.
 *
 * The binary does nothing except spin forever in userspace so we can
 * attach debuggers, observe scheduling behavior, or use it as a stable
 * target for migration-related experiments.
 */

int main(int argc, char *argv[]) {
  /* Stay in userspace indefinitely. */
  while (1)
    ;

  return 0;
}
