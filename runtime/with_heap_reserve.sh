#!/bin/sh
# Runtime support for the large finite import on 64-bit Linux with glibc.
set -eu
aes8_runtime_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
if [ "$#" -eq 0 ]; then
    printf '%s\n' 'Usage: sh runtime/with_heap_reserve.sh COMMAND [ARGUMENT ...]' >&2
    exit 2
fi
if [ ! -f "$aes8_runtime_dir/heap_reserve.so" ]; then
    printf '%s\n' 'Build runtime/heap_reserve.so as documented in README.md first.' >&2
    exit 2
fi
exec env \
    LD_PRELOAD="$aes8_runtime_dir/heap_reserve.so" \
    MALLOC_ARENA_MAX=1 \
    MALLOC_MMAP_MAX_=0 \
    MALLOC_PERTURB_=0 \
    MALLOC_TOP_PAD_=1073741824 \
    MALLOC_TRIM_THRESHOLD_=-1 \
    MIMALLOC_ALLOW_LARGE_OS_PAGES=0 \
    MIMALLOC_EAGER_COMMIT=1 \
    MIMALLOC_EAGER_COMMIT_DELAY=0 \
    MIMALLOC_PURGE_DELAY=-1 \
    MIMALLOC_RESERVE_OS_MEMORY=32G \
    "$@"
