#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static void stage(const char *name) {
  fprintf(stderr, "tz_globals_smoke stage=%s\n", name);
  fflush(stderr);
}

int main(void) {
  const char *tz = getenv("TZ");

  fprintf(stderr, "tz_globals_smoke TZ=%s\n", tz ? tz : "(unset)");
  fflush(stderr);

  stage("tzset");
  tzset();

  stage("read-globals");
  printf("tz_globals_smoke ok tzname0=%s tzname1=%s timezone=%ld daylight=%d\n",
         tzname[0] ? tzname[0] : "(null)",
         tzname[1] ? tzname[1] : "(null)",
         timezone, daylight);
  return 0;
}
