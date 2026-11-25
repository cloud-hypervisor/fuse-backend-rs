#!/bin/bash
# Quick sanity check: verify FUSE_WRITEBACK_CACHE is off by measuring write latency
set -u
BIN=/tmp/fuser-compare/target/release/passthrough
rm -rf /tmp/ft-src /tmp/ft-mnt && mkdir -p /tmp/ft-src /tmp/ft-mnt
"$BIN" /tmp/ft-src /tmp/ft-mnt 1 2>/dev/null &
PID=$!
sleep 1
dd if=/dev/urandom of=/tmp/ft-mnt/testfile bs=1M count=16 2>/dev/null
fio --name=test --filename=/tmp/ft-mnt/testfile --rw=randwrite --bs=4k --size=16M \
    --numjobs=1 --runtime=3 --time_based 2>&1 | grep -E 'WRITE|write:|lat.*avg'
kill $PID 2>/dev/null
wait $PID 2>/dev/null
fusermount3 -u /tmp/ft-mnt 2>/dev/null || true
