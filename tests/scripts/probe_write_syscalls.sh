#!/bin/bash
# Probe which write syscall each daemon uses for file payload writes
set -u
SRC=/tmp/ft-src
MNT=/tmp/ft-mnt

probe() {
    local name=$1 bin=$2
    shift 2
    rm -rf "$SRC" "$MNT" && mkdir -p "$SRC" "$MNT"
    "$bin" "$SRC" "$MNT" 2>/dev/null &
    local pid=$!
    sleep 1
    strace -f -e trace=write,writev,pwrite64,pwritev,pwritev2,sendfile -o /tmp/strace_$name.log -p $pid &
    local spid=$!
    sleep 0.2
    dd if=/dev/zero of="$MNT/probe" bs=128k count=64 2>/dev/null
    sync "$MNT/probe" 2>/dev/null
    sleep 0.5
    kill $spid 2>/dev/null
    wait $spid 2>/dev/null
    echo "=== $name ($*) ==="
    echo "--- syscall summary (only payload-carrying calls, ret >= 4096) ---"
    grep -oE '(writev?|pwrite(64|v|v2)?)\([^)]*\) = [0-9]+' /tmp/strace_$name.log \
        | awk '{n=$NF; if (n+0 >= 4096) print $1}' | sed 's/(.*//' | sort | uniq -c
    echo "--- payload size histogram ---"
    grep -oE '(writev?|pwrite(64|v|v2)?)\([^)]*\) = [0-9]+' /tmp/strace_$name.log \
        | grep -oE '[0-9]+$' | awk '$1 >= 4096' | sort -n | uniq -c | head -8
    kill $pid 2>/dev/null
    wait $pid 2>/dev/null
    fusermount3 -u "$MNT" 2>/dev/null || true
    sleep 0.5
}

probe backend /tmp/fuser-compare/target/release/passthrough 1
probe fuser /tmp/fuser-compare/target/release/passthrough-fuser
