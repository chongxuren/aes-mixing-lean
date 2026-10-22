/* Runtime support for the large finite import on 64-bit Linux with glibc.
 * No allocator/loader symbol is overridden. Non-Lean processes only read exe.
 */
#define _GNU_SOURCE 1
#include <errno.h>
#include <fcntl.h>
#include <malloc.h>
#include <stddef.h>
#include <stdint.h>
#include <unistd.h>

_Static_assert(sizeof(void *) == 8, "This launcher requires the pinned 64-bit runtime");
static const uint64_t reserve_bytes = UINT64_C(24) * 1024 * 1024 * 1024;

/* Use stack buffers and write, avoiding stdio or allocation in diagnostics. */
static char *append_text(char *out, const char *text) {
  while (*text) *out++ = *text++;
  return out;
}

static char *append_number(char *out, uint64_t value) {
  char digits[20];
  size_t used = 0;
  do { digits[used++] = (char)('0' + value % 10); value /= 10; } while (value);
  while (used) *out++ = digits[--used];
  return out;
}

static void emit(const char *data, size_t length) {
  while (length) {
    ssize_t written = write(STDERR_FILENO, data, length);
    if (written < 0 && errno == EINTR) continue;
    if (written <= 0) _exit(125);
    data += written;
    length -= (size_t)written;
  }
}

static void fail(const char *phase) {
  char line[256], *out = line;
  int saved_errno = errno;
  out = append_text(out, "AES8_HEAP_RESERVE_FAIL phase=");
  out = append_text(out, phase);
  out = append_text(out, " errno=");
  out = append_number(out, (uint64_t)(unsigned int)saved_errno);
  *out++ = '\n';
  emit(line, (size_t)(out - line));
  _exit(125);
}

static uint64_t count_maps(void) {
  char buffer[4096];
  uint64_t count = 0;
  int fd = open("/proc/self/maps", O_RDONLY | O_CLOEXEC);
  if (fd < 0) fail("maps-open");
  for (;;) {
    ssize_t size = read(fd, buffer, sizeof(buffer));
    if (size < 0 && errno == EINTR) continue;
    if (size < 0) fail("maps-read");
    if (!size) break;
    for (ssize_t i = 0; i < size; ++i) if (buffer[i] == '\n') ++count;
  }
  if (close(fd) != 0) fail("maps-close");
  return count;
}

static uintptr_t sample(const char *phase) {
  char line[256], *out = line;
  void *current = sbrk(0);
  if (current == (void *)-1) fail("sbrk");
  uint64_t maps = count_maps();
  out = append_text(out, "AES8_HEAP_RESERVE_SAMPLE phase=");
  out = append_text(out, phase);
  out = append_text(out, " pid=");
  out = append_number(out, (uint64_t)getpid());
  out = append_text(out, " brk=");
  out = append_number(out, (uint64_t)(uintptr_t)current);
  out = append_text(out, " maps=");
  out = append_number(out, maps);
  *out++ = '\n';
  emit(line, (size_t)(out - line));
  return (uintptr_t)current;
}

__attribute__((constructor)) static void reserve_main_heap(void) {
  char executable[4096];
  ssize_t size = readlink("/proc/self/exe", executable, sizeof(executable));
  if (size <= 0 || (size_t)size == sizeof(executable)) fail("exe-readlink");
  const char *base = executable;
  for (ssize_t i = 0; i < size; ++i) if (executable[i] == '/') base = executable + i + 1;
  if (executable + size - base != 4 || base[0] != 'l' || base[1] != 'e' ||
      base[2] != 'a' || base[3] != 'n') return;

  /* glibc 2.17: mallopt initializes/consolidates main_arena. The unsigned
   * trim maximum and no_dyn_threshold retain the freed main-heap top chunk.
   * M_PERTURB=0 prevents inherited settings from touching the 24 GiB payload.
   */
  if (!mallopt(M_MMAP_MAX, 0)) fail("mallopt-mmap-max");
  if (!mallopt(M_ARENA_MAX, 1)) fail("mallopt-arena-max");
  if (!mallopt(M_TRIM_THRESHOLD, -1)) fail("mallopt-trim");
  if (!mallopt(M_PERTURB, 0)) fail("mallopt-perturb");

  uintptr_t before = sample("before");
  void * volatile block = malloc((size_t)reserve_bytes);
  if (!block) fail("malloc");
  uintptr_t address = (uintptr_t)block;
  uintptr_t allocated = sample("allocated");
  if (allocated < before || allocated - before < reserve_bytes ||
      address > allocated || reserve_bytes > allocated - address) fail("not-main-heap");
  free(block);
  block = NULL;
  uintptr_t freed = sample("freed");
  if (freed != allocated || freed < before || freed - before < reserve_bytes)
    fail("heap-not-retained");

  char line[256], *out = line;
  out = append_text(out, "AES8_HEAP_RESERVE_OK bytes=");
  out = append_number(out, reserve_bytes);
  out = append_text(out, " retained_growth=");
  out = append_number(out, (uint64_t)(freed - before));
  out = append_text(out, " pid=");
  out = append_number(out, (uint64_t)getpid());
  *out++ = '\n';
  emit(line, (size_t)(out - line));
}
