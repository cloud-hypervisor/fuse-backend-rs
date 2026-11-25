#!/bin/bash
# Count syscalls issued by each daemon per file create (1000 files)
set -u
SRC=/tmp/ft-src
MNT=/tmp/ft-mnt

count_one() {
    local label=$1 bin=$2
    shift 2
    rm -rf "$SRC" "$MNT" && mkdir -p "$SRC" "$MNT"
    "$bin" "$SRC" "$MNT" "$@" 2>/dev/null &
    local pid=$!
    sleep 1
    strace -f -c -o /tmp/daemon_strace.log -p $pid &
    local spid=$!
    sleep 0.2
    python3 /tmp/create_bench.py "$MNT" 1000 > /dev/null
    sleep 0.3
    kill $spid 2>/dev/null
    wait $spid 2>/dev/null
    echo "=== $label: syscalls per 1000 creates ==="
    grep -vE '^% time|^\s*$|^strace|^Summary|^-+' /tmp/daemon_strace.log | awk '{print $NF, $4}' | head -20
    kill $pid 2>/dev/null
    wait $pid 2>/dev/null
    fusermount3 -u "$MNT" 2>/dev/null || true
    sleep 0.3
}

count_one "backend" /tmp/fuser-compare/target/release/passthrough 1
count_one "fuser" /tmp/fuser-compare/target/release/passthrough-fuser
