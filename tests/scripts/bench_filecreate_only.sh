#!/bin/bash
# filecreate-only benchmark: daemon x threads, single fio client thread
set -u
BIN_DIR=/tmp/fuser-compare/target/release
RESULTS_DIR=/tmp/fuser-compare-results
SRC_DIR=/tmp/fuser-compare-src
MNT_DIR=/tmp/fuser-compare-mnt

wait_mount() {
    for i in $(seq 1 30); do
        mountpoint -q "$MNT_DIR" 2>/dev/null && return 0
        sleep 0.1
    done
    return 1
}

run_one() {
    local daemon=$1 threads=$2 bin=$3
    shift 3
    rm -rf "$SRC_DIR" "$MNT_DIR" && mkdir -p "$SRC_DIR" "$MNT_DIR"
    "$bin" "$SRC_DIR" "$MNT_DIR" "$@" 2>/dev/null &
    local pid=$!
    if ! wait_mount; then
        echo "  ERROR: $daemon failed to mount"
        kill $pid 2>/dev/null
        return 1
    fi
    fio --name=filecreate \
        --directory="$MNT_DIR" \
        --rw=write --bs=4k --size=4k --nrfiles=5000 \
        --numjobs=1 --time_based --runtime=10 \
        --group_reporting --output-format=json \
        --output="$RESULTS_DIR/${daemon}_t${threads}_filecreate.json" 2>/dev/null || true
    kill $pid 2>/dev/null
    wait $pid 2>/dev/null
    fusermount3 -u "$MNT_DIR" 2>/dev/null || true
    sleep 0.5
}

for t in 1 2 4 8; do
    echo "=== threads=$t ==="
    echo -n "  backend filecreate... "
    run_one backend "$t" "$BIN_DIR/passthrough" "$t"
    echo "done"
    echo -n "  fuser filecreate... "
    run_one fuser "$t" "$BIN_DIR/passthrough-fuser"
    echo "done"
done
