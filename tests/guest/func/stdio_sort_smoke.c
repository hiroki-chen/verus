/*
 * Stdio and heap smoke test that writes a text dataset, parses it back,
 * sorts records in memory, emits a normalized output file, and re-reads it.
 */

#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define RECORD_COUNT 2048

struct record {
  int id;
  int score;
};

static void die_perror(const char *what) {
  perror(what);
  exit(1);
}

static int cmp_record(const void *lhs, const void *rhs) {
  const struct record *a = (const struct record *)lhs;
  const struct record *b = (const struct record *)rhs;

  if (a->score != b->score)
    return (a->score < b->score) ? -1 : 1;
  if (a->id != b->id)
    return (a->id < b->id) ? -1 : 1;
  return 0;
}

int main(void) {
  char in_path[] = "/tmp/stdio-sort-input.XXXXXX";
  char out_path[] = "/tmp/stdio-sort-output.XXXXXX";
  struct record *records;
  FILE *in;
  FILE *out;
  int in_fd;
  int out_fd;
  long long score_sum = 0;
  char line[128];

  in_fd = mkstemp(in_path);
  if (in_fd < 0)
    die_perror("mkstemp input");
  out_fd = mkstemp(out_path);
  if (out_fd < 0)
    die_perror("mkstemp output");

  in = fdopen(in_fd, "w+");
  if (!in)
    die_perror("fdopen input");
  out = fdopen(out_fd, "w+");
  if (!out)
    die_perror("fdopen output");

  for (int i = 0; i < RECORD_COUNT; i++) {
    int score = (i * 37 + 19) % 997;
    fprintf(in, "%d,%d\n", i, score);
  }
  fflush(in);
  rewind(in);

  records = calloc(RECORD_COUNT, sizeof(*records));
  if (!records)
    die_perror("calloc");

  for (int i = 0; i < RECORD_COUNT; i++) {
    if (!fgets(line, sizeof(line), in)) {
      fprintf(stderr, "stdio_sort_smoke: short read at record %d\n", i);
      return 1;
    }
    if (sscanf(line, "%d,%d", &records[i].id, &records[i].score) != 2) {
      fprintf(stderr, "stdio_sort_smoke: parse failure: %s\n", line);
      return 1;
    }
  }

  qsort(records, RECORD_COUNT, sizeof(*records), cmp_record);

  for (int i = 0; i < RECORD_COUNT; i++) {
    if (i > 0 && records[i - 1].score > records[i].score) {
      fprintf(stderr, "stdio_sort_smoke: sort order broken at %d\n", i);
      return 1;
    }
    score_sum += records[i].score;
    fprintf(out, "%04d:%04d\n", records[i].score, records[i].id);
  }

  fflush(out);
  rewind(out);

  for (int i = 0; i < 8; i++) {
    if (!fgets(line, sizeof(line), out)) {
      fprintf(stderr, "stdio_sort_smoke: short output read at %d\n", i);
      return 1;
    }
  }

  free(records);
  fclose(in);
  fclose(out);
  unlink(in_path);
  unlink(out_path);

  printf("stdio_sort_smoke ok records=%d score_sum=%lld\n", RECORD_COUNT,
         score_sum);
  return 0;
}
