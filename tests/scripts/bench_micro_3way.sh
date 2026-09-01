#!/bin/bash
# Interleaved 3-way microbenchmark: backend-epoll vs backend-blocking vs fuser.
# Each round runs all implementations back-to-back so host-state drift
# (frequency/scheduler) affects them equally.
# Results appended to $OUT in parseable form:
#   impl workers procs round ops_s lat_us
set -u

ROUNDS=${1:-5}
OUT=/tmp/micro-3way-results.txt

BACK_BIN=/tmp/fuse-blocking/target/release/passthrough
FUSER_BIN=/tmp/fuser-compare/target/release/passthrough-fuser
MICRO=/tmp/fuse-blocking/tests/scripts/micro_read_ab.py
SRC=/tmp/fuse-blocking/data
MNT=/tmp/mnt-3way

mkdir -p "$SRC" "$MNT"
: > "$OUT"

cleanup() {
    pkill -x passthrough 2>/dev/null
    pkill -x passthrough-fuser 2>/dev/null
    sleep 1
    fusermount3 -u "$MNT" 2>/dev/null
}
trap cleanup EXIT

# run_one <label> <workers> -- starts daemon named by $1/$2, runs micro, appends
run_daemon() { # impl workers blocking_or_fuser round
    local impl=$1 workers=$2 flag=$3 round=$4
    rm -rf "$SRC"/*
    if [ "$impl" = "fuser" ]; then
        "$FUSER_BIN" "$SRC" "$MNT" >/dev/null 2>&1 &
    else
        "$BACK_BIN" "$SRC" "$MNT" "$workers" "$flag" >/dev/null 2>&1 &
    fi
    local dp=$!
    sleep 2
    if ! kill -0 "$dp" 2>/dev/null; then
        echo "  $impl w=$workers: daemon died on startup" >&2
        return
    fi
    dd if=/dev/zero of="$MNT/testfile" bs=1048576 count=1024 conv=fsync >/dev/null 2>&1
    sync
    for procs in 1 4; do
        local line
        line=$(python3 "$MICRO" "$MNT" "$procs" 40000 | tail -1)
        local ops lat
        ops=$(echo "$line" | grep -o 'throughput=[0-9]*' | cut -d= -f2)
        lat=$(echo "$line" | grep -o 'per_proc_mean=[0-9.]*' | cut -d= -f2)
        echo "$impl $workers $procs $round $ops $lat" >> "$OUT"
    done
    kill "$dp" 2>/dev/null
    wait "$dp" 2>/dev/null
    sleep 1
}

for r in $(seq 1 "$ROUNDS"); do
    echo "===== round $r $(date '+%H:%M:%S') ====="
    run_daemon epoll  1 false "$r"
    run_daemon epoll  2 false "$r"
    run_daemon epoll  4 false "$r"
    run_daemon block  1 true  "$r"
    run_daemon block  2 true  "$r"
    run_daemon block  4 true  "$r"
    run_daemon fuser  1 -     "$r"
done
echo "ALL ROUNDS DONE"
