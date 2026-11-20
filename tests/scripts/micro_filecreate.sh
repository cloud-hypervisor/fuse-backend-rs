#!/bin/bash
# Microbenchmark: time creating N files through the mount (wall clock).
# Avoids fio's create-path measurement noise.
set -u
BIN=/tmp/fuser-compare/target/release/passthrough
SRC=/tmp/ft-src
MNT=/tmp/ft-mnt
N=5000
ROUNDS=3

for r in $(seq 1 $ROUNDS); do
    rm -rf "$SRC" "$MNT" && mkdir -p "$SRC" "$MNT"
    "$BIN" "$SRC" "$MNT" 1 2>/dev/null &
    PID=$!
    sleep 1
    START=$(date +%s.%N)
    for i in $(seq 1 $N); do
        touch "$MNT/f$i"
    done
    END=$(date +%s.%N)
    ELAPSED=$(echo "$END $START" | awk '{printf "%.2f", $1-$2}')
    PER_FILE=$(echo "$ELAPSED $N" | awk '{printf "%.1f", $1*1e6/$2}')
    echo "backend(nocred) round$r: ${ELAPSED}s total, ${PER_FILE} us/file"
    kill $PID 2>/dev/null
    wait $PID 2>/dev/null
    fusermount3 -u "$MNT" 2>/dev/null || true
    sleep 0.3
done
