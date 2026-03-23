#include <errno.h>
#include <locale.h>
#include <pthread.h>
#include <semaphore.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/random.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

static pthread_key_t g_key;
static pthread_mutex_t g_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t g_cv = PTHREAD_COND_INITIALIZER;
static sem_t g_sem;
static __thread uint64_t g_tls_word = 0xabcddcba11223344ULL;

static void stage(const char *name) {
  fprintf(stderr, "python_runtime_early_smoke stage=%s\n", name);
  fflush(stderr);
}

static void *worker_main(void *arg) {
  uint64_t local = (uint64_t)(uintptr_t)arg ^ 0x55aa55aa55aa55aaULL;
  int rc;

  g_tls_word ^= local;

  rc = pthread_setspecific(g_key, (void *)(uintptr_t)g_tls_word);
  if (rc != 0) {
    fprintf(stderr, "pthread_setspecific failed rc=%d\n", rc);
    return (void *)1;
  }

  rc = sem_post(&g_sem);
  if (rc != 0) {
    perror("sem_post");
    return (void *)1;
  }

  rc = pthread_mutex_lock(&g_mu);
  if (rc != 0) {
    fprintf(stderr, "pthread_mutex_lock failed rc=%d\n", rc);
    return (void *)1;
  }

  rc = pthread_cond_signal(&g_cv);
  if (rc != 0) {
    fprintf(stderr, "pthread_cond_signal failed rc=%d\n", rc);
    pthread_mutex_unlock(&g_mu);
    return (void *)1;
  }

  rc = pthread_mutex_unlock(&g_mu);
  if (rc != 0) {
    fprintf(stderr, "pthread_mutex_unlock failed rc=%d\n", rc);
    return (void *)1;
  }

  return NULL;
}

int main(void) {
  pthread_t th;
  pthread_condattr_t cv_attr;
  struct sigaction sa;
  struct timespec ts;
  void *joined = NULL;
  unsigned char randbuf[16];
  char *lang = NULL;
  int rc;

  memset(&sa, 0, sizeof(sa));
  sa.sa_handler = SIG_IGN;
  sigemptyset(&sa.sa_mask);

  stage("sigaction-sigpipe");
  if (sigaction(SIGPIPE, &sa, NULL) != 0) {
    perror("sigaction(SIGPIPE)");
    return 1;
  }

  stage("sigaction-sigxfsz");
  if (sigaction(SIGXFSZ, &sa, NULL) != 0) {
    perror("sigaction(SIGXFSZ)");
    return 1;
  }

  stage("setlocale");
  if (setlocale(LC_ALL, "") == NULL) {
    fprintf(stderr, "setlocale failed\n");
    return 1;
  }

  stage("setenv");
  if (setenv("PY_RUNTIME_EARLY_SMOKE", "enabled", 1) != 0) {
    perror("setenv");
    return 1;
  }

  stage("getenv");
  lang = getenv("LANG");
  if (getenv("PY_RUNTIME_EARLY_SMOKE") == NULL) {
    fprintf(stderr, "getenv after setenv failed\n");
    return 1;
  }

  stage("getrandom");
  if (getrandom(randbuf, sizeof(randbuf), 0) != (ssize_t)sizeof(randbuf)) {
    perror("getrandom");
    return 1;
  }

  stage("clock_gettime");
  if (clock_gettime(CLOCK_REALTIME, &ts) != 0) {
    perror("clock_gettime");
    return 1;
  }

  stage("localtime_r");
  if (localtime_r(&ts.tv_sec, &(struct tm){0}) == NULL && errno != 0) {
    perror("localtime_r");
    return 1;
  }

  stage("after-localtime_r");

  stage("before-pthread_key_create");
  stage("pthread_key_create");
  rc = pthread_key_create(&g_key, NULL);
  if (rc != 0) {
    fprintf(stderr, "pthread_key_create failed rc=%d\n", rc);
    return 1;
  }

  stage("pthread_condattr_init");
  rc = pthread_condattr_init(&cv_attr);
  if (rc != 0) {
    fprintf(stderr, "pthread_condattr_init failed rc=%d\n", rc);
    return 1;
  }

  stage("pthread_condattr_setclock");
  rc = pthread_condattr_setclock(&cv_attr, CLOCK_REALTIME);
  if (rc != 0) {
    fprintf(stderr, "pthread_condattr_setclock failed rc=%d\n", rc);
    pthread_condattr_destroy(&cv_attr);
    return 1;
  }

  stage("pthread_cond_init");
  rc = pthread_cond_init(&g_cv, &cv_attr);
  pthread_condattr_destroy(&cv_attr);
  if (rc != 0) {
    fprintf(stderr, "pthread_cond_init failed rc=%d\n", rc);
    return 1;
  }

  stage("sem_init");
  if (sem_init(&g_sem, 0, 0) != 0) {
    perror("sem_init");
    return 1;
  }

  stage("pthread_mutex_lock");
  rc = pthread_mutex_lock(&g_mu);
  if (rc != 0) {
    fprintf(stderr, "pthread_mutex_lock failed rc=%d\n", rc);
    return 1;
  }

  stage("pthread_create");
  rc = pthread_create(&th, NULL, worker_main, (void *)(uintptr_t)getpid());
  if (rc != 0) {
    fprintf(stderr, "pthread_create failed rc=%d\n", rc);
    pthread_mutex_unlock(&g_mu);
    return 1;
  }

  stage("pthread_cond_wait");
  rc = pthread_cond_wait(&g_cv, &g_mu);
  if (rc != 0) {
    fprintf(stderr, "pthread_cond_wait failed rc=%d\n", rc);
    pthread_mutex_unlock(&g_mu);
    return 1;
  }

  stage("pthread_mutex_unlock");
  rc = pthread_mutex_unlock(&g_mu);
  if (rc != 0) {
    fprintf(stderr, "pthread_mutex_unlock failed rc=%d\n", rc);
    return 1;
  }

  stage("sem_wait");
  if (sem_wait(&g_sem) != 0) {
    perror("sem_wait");
    return 1;
  }

  stage("pthread_join");
  rc = pthread_join(th, &joined);
  if (rc != 0) {
    fprintf(stderr, "pthread_join failed rc=%d\n", rc);
    return 1;
  }

  if (joined != NULL) {
    fprintf(stderr, "worker returned failure marker=%p\n", joined);
    return 1;
  }

  stage("sem_destroy");
  if (sem_destroy(&g_sem) != 0) {
    perror("sem_destroy");
    return 1;
  }

  stage("done");
  pthread_key_delete(g_key);

  printf("python_runtime_early_smoke ok tls=0x%llx lang=%s rand0=%u sec=%lld\n",
         (unsigned long long)g_tls_word, lang ? lang : "(null)",
         (unsigned)randbuf[0], (long long)ts.tv_sec);
  return 0;
}
