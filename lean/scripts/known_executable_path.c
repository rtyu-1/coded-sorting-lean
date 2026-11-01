/* Local startup compatibility for a filesystem without /proc/PID/exe.
   This supplies only the explicitly configured known executable path.
   It does not read /proc or change Lean's executable, libraries, or kernel. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

ssize_t readlink(const char *path, char *buf, size_t size) {
    char own_exe[80];
    snprintf(own_exe, sizeof(own_exe), "/proc/%ld/exe", (long)getpid());
    const char *known = getenv("CODED_SORTING_KNOWN_EXE");
    if (known && (strcmp(path, own_exe) == 0 || strcmp(path, "/proc/self/exe") == 0)) {
        size_t n = strlen(known);
        if (n > size) n = size;
        memcpy(buf, known, n);
        return (ssize_t)n;
    }
    ssize_t (*original)(const char *, char *, size_t) = dlsym(RTLD_NEXT, "readlink");
    if (!original) { errno = ENOSYS; return -1; }
    return original(path, buf, size);
}
