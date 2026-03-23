#include <errno.h>
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static void stage(const char *name) {
  fprintf(stderr, "localtime_smoke stage=%s\n", name);
  fflush(stderr);
}

int main(void) {
  time_t now;
  struct tm local_tm;
  struct tm gmt_tm;
  char local_out[128];
  char gmt_out[128];
  const char *tz;

  memset(&local_tm, 0, sizeof(local_tm));
  memset(&gmt_tm, 0, sizeof(gmt_tm));
  memset(local_out, 0, sizeof(local_out));
  memset(gmt_out, 0, sizeof(gmt_out));

  tz = getenv("TZ");
  fprintf(stderr, "localtime_smoke TZ=%s\n", tz ? tz : "(unset)");
  fflush(stderr);

  stage("setlocale");
  if (setlocale(LC_ALL, "") == NULL) {
    fprintf(stderr, "setlocale failed\n");
    return 1;
  }

  stage("time");
  now = time(NULL);
  if (now == (time_t)-1) {
    perror("time");
    return 1;
  }

  stage("tzset");
  tzset();

  stage("gmtime_r");
  if (gmtime_r(&now, &gmt_tm) == NULL) {
    perror("gmtime_r");
    return 1;
  }

  stage("strftime-gmt");
  if (strftime(gmt_out, sizeof(gmt_out), "%Y-%m-%d %H:%M:%S UTC", &gmt_tm) == 0) {
    fprintf(stderr, "strftime gmt failed\n");
    return 1;
  }

  stage("localtime_r");
  if (localtime_r(&now, &local_tm) == NULL) {
    perror("localtime_r");
    return 1;
  }

  stage("strftime-local");
  if (strftime(local_out, sizeof(local_out), "%Y-%m-%d %H:%M:%S %Z", &local_tm) == 0) {
    fprintf(stderr, "strftime local failed\n");
    return 1;
  }

  printf("localtime_smoke ok gmt=%s local=%s\n", gmt_out, local_out);
  return 0;
}
