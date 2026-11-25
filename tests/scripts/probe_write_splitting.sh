#!/bin/bash
# Measure how the kernel splits 128k writes for each daemon:
# count pwrite syscalls and their sizes while dd'ing 8MB through the mount.
set -u
BIN_BACKEND=/tmp/fuser-compare/target/release/passthrough
BIN_FUSER=/tmp/fuser-compare/target/release/passthrough-fuser
SRC=/tmp/ft-src
MNT=/tmp/ft-mnt

which strace >/dev/null 2>&1 || { echo "NO_STRACE"; exit 1; }

measure() {
    local name=$1 bin=$2
    rm -rf "$SRC" "$MNT" && mkdir -p "$SRC" "$MNT"
    "$bin" "$SRC" "$MNT" 2>/dev/null &
    local pid=$!
    sleep 1
    # dd 8MB in 128k blocks through the mount, while tracing the daemon's pwrite calls
    strace -f -e trace=pwrite64,write -o /tmp/strace_$name.log -p $pid &
    local spid=$!
    sleep 0.2
    dd if=/dev/zero of="$MNT/probe" bs=128k count=64 conv=fdatasync 2>/dev/null
    sleep 0.5
    kill $spid 2>/dev/null
    wait $spid 2>/dev/null
    echo "=== $name: 8MB dd in 128k blocks ==="
    # histogram of pwrite64 size arguments (file writes issued by the daemon)
    echo "--- pwrite64 size histogram (count x size) ---"
    grep -oE 'pwrite64\([^)]*\) = [0-9]+' /tmp/strace_$name.log \
        | grep -oE '[0-9]+$' | sort | uniq -c | sort -rn | head -8
    echo "--- total pwrite64 calls ---"
    grep -cE 'pwrite64\(' /tmp/strace_$name.log
    kill $pid 2>/dev/null
    wait $pid 2>/dev/null
    fusermount3 -u "$MNT" 2>/dev/null || true
    sleep 0.5
}

measure backend "$BIN_BACKEND"
measure fuser "$BIN_FUSER"
