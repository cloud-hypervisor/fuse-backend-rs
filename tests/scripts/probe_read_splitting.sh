#!/bin/bash
# Probe READ request sizes seen by each daemon (pread calls) during a sequential read
set -u
SRC=/tmp/ft-src
MNT=/tmp/ft-mnt

probe() {
    local name=$1 bin=$2
    rm -rf "$SRC" "$MNT" && mkdir -p "$SRC" "$MNT"
    "$bin" "$SRC" "$MNT" 2>/dev/null &
    local pid=$!
    sleep 1
    # create file directly in source dir, 8MB
    dd if=/dev/zero of="$SRC/probe" bs=128k count=64 2>/dev/null
    strace -f -e trace=read,pread64,readv,preadv,sendfile,splice -o /tmp/strace_rd_$name.log -p $pid &
    local spid=$!
    sleep 0.2
    # sequential read through mount, 128k blocks, fresh page cache
    dd if="$MNT/probe" of=/dev/null bs=128k count=64 iflag=nocache 2>/dev/null \
        || dd if="$MNT/probe" of=/dev/null bs=128k count=64 2>/dev/null
    sleep 0.5
    kill $spid 2>/dev/null
    wait $spid 2>/dev/null
    echo "=== $name: 8MB seqread in 128k blocks ==="
    echo "--- payload read size histogram (ret >= 4096) ---"
    grep -oE '(pread64|readv|preadv|sendfile|splice)\([^)]*\) = [0-9]+' /tmp/strace_rd_$name.log \
        | grep -oE '[0-9]+$' | awk '$1 >= 4096' | sort -n | uniq -c | head -8
    echo "--- raw read() (dev/fuse) size histogram (ret >= 4096) ---"
    grep -oE '\bread\([^)]*\) = [0-9]+' /tmp/strace_rd_$name.log \
        | grep -oE '[0-9]+$' | awk '$1 >= 4096' | sort -n | uniq -c | head -8
    kill $pid 2>/dev/null
    wait $pid 2>/dev/null
    fusermount3 -u "$MNT" 2>/dev/null || true
    sleep 0.5
}

probe backend "/tmp/fuser-compare/target/release/passthrough 1"
probe fuser /tmp/fuser-compare/target/release/passthrough-fuser
