#define _GNU_SOURCE

#include <arpa/inet.h>
#include <ctype.h>
#include <dirent.h>
#include <dlfcn.h>
#include <errno.h>
#include <expat.h>
#include <fcntl.h>
#include <grp.h>
#include <langinfo.h>
#include <locale.h>
#include <math.h>
#include <netdb.h>
#include <pwd.h>
#include <sched.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sys/mman.h>
#include <sys/random.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/utsname.h>
#include <time.h>
#include <unistd.h>
#include <zlib.h>

extern char **environ;

__thread uint64_t reloc_tls = 0xa5a5b4b4c3c3d2d2ULL;

static unsigned char reloc_blob[512 * 1024];
static uint64_t reloc_words[8192];
static char reloc_banner[1024];

static void fatal(const char *what) {
  perror(what);
  exit(1);
}

static unsigned long checksum_xml = 0;

static void xml_start(void *userdata, const XML_Char *name,
                      const XML_Char **attrs) {
  (void)userdata;
  checksum_xml ^= (unsigned long)name[0];
  if (attrs && attrs[0] && attrs[1])
    checksum_xml += (unsigned long)attrs[1][0];
}

static void xml_end(void *userdata, const XML_Char *name) {
  (void)userdata;
  checksum_xml ^= (unsigned long)name[0] << 7;
}

static void fill_state(void) {
  for (size_t i = 0; i < sizeof(reloc_blob); ++i)
    reloc_blob[i] = (unsigned char)((i * 13u + 29u) & 0xffu);

  for (size_t i = 0; i < sizeof(reloc_words) / sizeof(reloc_words[0]); ++i)
    reloc_words[i] = 0x9e3779b97f4a7c15ULL ^ ((uint64_t)i << 11);

  snprintf(reloc_banner, sizeof(reloc_banner),
           "python_reloc_heavy_smoke pid=%ld stdin=%p stdout=%p stderr=%p",
           (long)getpid(), (void *)stdin, (void *)stdout, (void *)stderr);
}

static uint64_t touch_state(void) {
  uint64_t acc = reloc_tls;

  for (size_t i = 0; i < sizeof(reloc_blob); i += 128)
    acc = (acc * 11400714819323198485ULL) ^ reloc_blob[i];

  for (size_t i = 0; i < sizeof(reloc_words) / sizeof(reloc_words[0]); ++i)
    acc ^= reloc_words[i] + (uint64_t)i * 97ULL;

  for (size_t i = 0; reloc_banner[i] != '\0'; ++i)
    acc ^= (uint64_t)(unsigned char)reloc_banner[i] << (i & 7);

  return acc;
}

static uint64_t compress_blob(void) {
  uLongf dst_len = compressBound(sizeof(reloc_blob));
  Bytef *dst = malloc(dst_len);
  uint64_t acc = 0;

  if (!dst) {
    fprintf(stderr, "malloc failed\n");
    exit(1);
  }

  if (compress2(dst, &dst_len, reloc_blob, sizeof(reloc_blob), Z_BEST_SPEED) !=
      Z_OK) {
    fprintf(stderr, "compress2 failed\n");
    free(dst);
    exit(1);
  }

  for (uLongf i = 0; i < dst_len; i += 257)
    acc = (acc << 9) ^ (acc >> 3) ^ dst[i];

  free(dst);
  return acc ^ dst_len;
}

static void parse_xml(void) {
  static const char xml[] =
      "<root><pkg name='python'/><pkg name='expat'/><pkg name='zlib'/></root>";
  XML_Parser parser = XML_ParserCreate(NULL);

  if (!parser) {
    fprintf(stderr, "XML_ParserCreate failed\n");
    exit(1);
  }

  XML_SetElementHandler(parser, xml_start, xml_end);
  if (XML_Parse(parser, xml, (int)strlen(xml), XML_TRUE) == XML_STATUS_ERROR) {
    fprintf(stderr, "XML_Parse failed\n");
    XML_ParserFree(parser);
    exit(1);
  }

  XML_ParserFree(parser);
}

static uint64_t exercise_import_like_calls(void) {
  struct utsname uts;
  struct rlimit rl;
  struct timeval tv;
  struct timespec ts;
  struct stat st;
  struct dirent *de;
  DIR *dir;
  uint64_t acc = 0;
  unsigned char rnd[32];
  char exe[512];
  char host[128];
  char addrbuf[INET_ADDRSTRLEN];
  struct in_addr loop = {.s_addr = htonl(INADDR_LOOPBACK)};
  struct passwd *pw;
  struct group *gr;
  locale_t loc;
  locale_t old_loc;
  char *endp = NULL;
  int pipes[2];
  int spair[2];
  char io_buf[64];

  if (uname(&uts) != 0)
    fatal("uname");
  if (getrlimit(RLIMIT_STACK, &rl) != 0)
    fatal("getrlimit");
  if (gettimeofday(&tv, NULL) != 0)
    fatal("gettimeofday");
  if (clock_gettime(CLOCK_REALTIME, &ts) != 0)
    fatal("clock_gettime");
  if (getrandom(rnd, sizeof(rnd), 0) != (ssize_t)sizeof(rnd))
    fatal("getrandom");
  if (readlink("/proc/self/exe", exe, sizeof(exe) - 1) < 0)
    fatal("readlink");
  if (stat("/usr/lib", &st) != 0)
    fatal("stat");

  dir = opendir("/usr/lib");
  if (!dir)
    fatal("opendir");
  while ((de = readdir(dir)) != NULL)
    acc ^= (uint64_t)(unsigned char)de->d_name[0] << ((acc >> 2) & 7);
  closedir(dir);

  if (!inet_ntop(AF_INET, &loop, addrbuf, sizeof(addrbuf))) {
    fprintf(stderr, "inet_ntop failed\n");
    exit(1);
  }

  if (gethostname(host, sizeof(host)) != 0)
    fatal("gethostname");

  pw = getpwuid(getuid());
  gr = getgrgid(getgid());

  loc = newlocale(LC_ALL_MASK, "C.UTF-8", (locale_t)0);
  if (!loc)
    fatal("newlocale");
  old_loc = uselocale(loc);
  if (!old_loc) {
    freelocale(loc);
    fatal("uselocale");
  }

  acc ^= (uint64_t)strtoull("12345", &endp, 10);
  acc ^= (uint64_t)strtod("3.14159", &endp);
  acc ^= (uint64_t)toupper((unsigned char)'p');
  acc ^= (uint64_t)tolower((unsigned char)'Y');
  acc ^= (uint64_t)isalpha((unsigned char)'z');
  acc ^= (uint64_t)nl_langinfo(CODESET)[0];
  acc ^= (uint64_t)sched_getcpu();
  acc ^= (uint64_t)sysconf(_SC_PAGESIZE);
  acc ^= (uint64_t)strlen(uts.sysname);
  acc ^= (uint64_t)strlen(addrbuf);
  acc ^= (uint64_t)strlen(host);
  acc ^= (uint64_t)(pw ? pw->pw_uid : 0);
  acc ^= (uint64_t)(gr ? gr->gr_gid : 0);
  acc ^= rl.rlim_cur;
  acc ^= (uint64_t)tv.tv_sec ^ (uint64_t)ts.tv_nsec;
  acc ^= rnd[0];

  if (pipe2(pipes, O_CLOEXEC) != 0)
    fatal("pipe2");
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, spair) != 0)
    fatal("socketpair");

  memset(io_buf, 0, sizeof(io_buf));
  if (write(pipes[1], reloc_banner, 16) != 16)
    fatal("write pipe");
  if (read(pipes[0], io_buf, 16) != 16)
    fatal("read pipe");
  if (send(spair[0], reloc_banner, 12, 0) != 12)
    fatal("send");
  if (recv(spair[1], io_buf, 12, 0) != 12)
    fatal("recv");

  close(pipes[0]);
  close(pipes[1]);
  close(spair[0]);
  close(spair[1]);
  if (!uselocale(old_loc))
    fatal("restore uselocale");
  freelocale(loc);

  return acc;
}

static void exercise_mapping(void) {
  const size_t len = 8 * 4096;
  unsigned char *map = mmap(NULL, len, PROT_READ | PROT_WRITE,
                            MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);

  if (map == MAP_FAILED)
    fatal("mmap");

  memset(map, 0xa5, len);

  if (mprotect(map, len, PROT_READ) != 0)
    fatal("mprotect");

  if (map[0] != 0xa5 || map[len - 1] != 0xa5) {
    fprintf(stderr, "mapping verification failed\n");
    munmap(map, len);
    exit(1);
  }

  if (munmap(map, len) != 0)
    fatal("munmap");
}

int main(void) {
  uint64_t state_acc;
  uint64_t z_acc;
  uint64_t import_acc;
  double trig;
  size_t env_count = 0;

  fill_state();
  parse_xml();
  state_acc = touch_state();
  z_acc = compress_blob();
  import_acc = exercise_import_like_calls();
  exercise_mapping();

  trig = cos(0.25) + sin(0.75) + tanh(0.5) + sqrt(16.0);

  for (char **p = environ; p && *p; ++p)
    env_count++;

  printf("python_reloc_heavy_smoke ok tls=0x%llx state=0x%llx z=0x%llx "
         "import=0x%llx "
         "xml=%lu trig=%.6f env=%zu banner=%s\n",
         (unsigned long long)reloc_tls, (unsigned long long)state_acc,
         (unsigned long long)z_acc, (unsigned long long)import_acc,
         checksum_xml, trig, env_count, reloc_banner);

  return 0;
}
