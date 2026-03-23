/*
 * Small dynamic loading smoke test.
 *
 * This exercises ld.so plus the explicit dlopen/dlsym/dlclose path with
 * minimal extra runtime behavior.
 */

#define _GNU_SOURCE

#include <dlfcn.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

typedef double (*cos_fn_t)(double);

static void die_dl(const char *what) {
  const char *err = dlerror();
  fprintf(stderr, "%s: %s\n", what, err ? err : "unknown dlerror");
  exit(1);
}

int main(void) {
  void *handle;
  cos_fn_t cos_fn;
  double value;

  handle = dlopen("libm.so.6", RTLD_NOW | RTLD_LOCAL);
  if (!handle)
    die_dl("dlopen libm.so.6");

  dlerror();
  cos_fn = (cos_fn_t)dlsym(handle, "cos");
  if (!cos_fn)
    die_dl("dlsym cos");

  value = cos_fn(0.0);
  if (value < 0.999999 || value > 1.000001) {
    fprintf(stderr, "dlopen_smoke: unexpected cos(0.0)=%f\n", value);
    return 1;
  }

  if (dlclose(handle) != 0)
    die_dl("dlclose");

  printf("dlopen_smoke ok cos(0.0)=%.6f\n", value);
  return 0;
}
