#!/bin/bash
# Benchmark: fuse-backend-rs vs fuser passthrough filesystems.
#
# Runs the same fio workloads against two passthrough daemons — one built
# on this crate, one on the fuser library — and prints a per-workload
# delta table (parse_library_compare.py). Both daemons run with the FUSE
# writeback cache off (the backend one via --no-writeback; fuser cannot
# negotiate it at all), so the write path compares like for like. Reading
# the deltas rather than the absolute numbers keeps a shared CI runner
# usable: both sides are measured in the same job, so runner drift cancels.
#
# Requirements: Linux, fio, python3, permission to mount fuse (root or
# fusermount). The fuser daemon mounts through the fusermount3 helper and
# uses AutoUnmount with SessionACL::All, which also needs user_allow_other
# in /etc/fuse.conf.
#
# Environment knobs (all optional):
#   BACKEND_BIN    fuse-backend-rs daemon; must accept
#                  "<src> <mnt> --threads N" (default: the tests/benchmark
#                  binary under target/release)
#   FUSER_BIN      fuser daemon; must accept "<src> <mnt> -t N"
#                  (default: the passthrough-fuser binary under
#                  target/release)
#   BACKEND_EXTRA  extra args for the backend daemon (e.g. "--sync-blocking")
#   FUSER_EXTRA    extra args for the fuser daemon (e.g. "--no-clone-fd")
#   THREADS_LIST   space-separated thread counts (default "1 8"; the local
#                  runs that produced docs/fuse-library-comparison.md used
#                  "1 2 4 8")
#   RUNTIME        seconds per workload (default 10)
#   RESULTS_DIR    where the fio JSON results go
#   SRC_DIR        backing directory served through the mounts
#   MNT_DIR        mountpoint directory
#
# Usage: run the script as root (or with fusermount permissions) from the
# workspace root after building both daemons in release mode. Progress goes
# to stderr; the results table goes to stdout, so CI can append stdout to
# GITHUB_STEP_SUMMARY while the log keeps the progress lines.
set -euo pipefail

BACKEND_BIN="${BACKEND_BIN:-target/release/fuse-backend-rs-benchmark}"
FUSER_BIN="${FUSER_BIN:-target/release/passthrough-fuser}"
RESULTS_DIR="${RESULTS_DIR:-fuser-compare-results}"
SRC_DIR="${SRC_DIR:-/tmp/fuser-compare-src}"
MNT_DIR="${MNT_DIR:-/tmp/fuser-compare-mnt}"
THREADS_LIST="${THREADS_LIST:-1 8}"
RUNTIME="${RUNTIME:-10}"
BACKEND_EXTRA="${BACKEND_EXTRA:-}"
FUSER_EXTRA="${FUSER_EXTRA:-}"

DAEMON_PID=""

log() {
    echo "$@" >&2
}

# Workloads: fixed-amount work (nrfiles) rather than time_based, so the
# same amount of work is measured on both daemons regardless of speed.
run_workload() {
    local name=$1 rw=$2 bs=$3 size=$4 nrfiles=$5 outfile=$6 extra=${7:-}

    fio --name="$name" \
        --directory="$MNT_DIR" \
        --rw="$rw" \
        --bs="$bs" \
        --size="$size" \
        --nrfiles="$nrfiles" \
        --numjobs=1 \
        --time_based \
        --runtime="${RUNTIME}" \
        --group_reporting \
        --output-format=json \
        --output="$outfile" \
        $extra \
        2>/dev/null
}

run_multithread_workload() {
    local name=$1 rw=$2 bs=$3 size=$4 nrfiles=$5 numjobs=$6 outfile=$7 extra=${8:-}

    fio --name="$name" \
        --directory="$MNT_DIR" \
        --rw="$rw" \
        --bs="$bs" \
        --size="$size" \
        --nrfiles="$nrfiles" \
        --numjobs="$numjobs" \
        --time_based \
        --runtime="${RUNTIME}" \
        --group_reporting \
        --output-format=json \
        --output="$outfile" \
        $extra \
        2>/dev/null
}

# start_backend <threads>: the tests/benchmark daemon with the writeback
# cache off, so the write path matches fuser's (which cannot negotiate
# FUSE_WRITEBACK_CACHE). The daemon's stdout/stderr go to a log file
# under RESULTS_DIR, not to this script's streams: the results table is
# printed on stdout, and a child inheriting it would interleave its log
# lines into the table.
start_backend() {
    local threads=$1
    rm -rf "$SRC_DIR" "$MNT_DIR"
    mkdir -p "$SRC_DIR" "$MNT_DIR"
    # shellcheck disable=SC2086
    "$BACKEND_BIN" "$SRC_DIR" "$MNT_DIR" --no-writeback --threads "$threads" $BACKEND_EXTRA \
        > "$RESULTS_DIR/backend.log" 2>&1 &
    DAEMON_PID=$!
    wait_for_mount "fuse-backend-rs" "$DAEMON_PID"
}

start_fuser() {
    local threads=$1
    rm -rf "$SRC_DIR" "$MNT_DIR"
    mkdir -p "$SRC_DIR" "$MNT_DIR"
    # shellcheck disable=SC2086
    "$FUSER_BIN" "$SRC_DIR" "$MNT_DIR" -t "$threads" $FUSER_EXTRA \
        > "$RESULTS_DIR/fuser.log" 2>&1 &
    DAEMON_PID=$!
    wait_for_mount "fuser" "$DAEMON_PID"
}

# Wait up to 5s for the mountpoint to appear, checking daemon liveness first
# so a daemon that mounted and immediately died (leaving a stale mount) is
# never taken for success.
wait_for_mount() {
    local daemon=$1 pid=$2
    for _ in $(seq 50); do
        if ! kill -0 "$pid" 2>/dev/null; then
            log "  ERROR: $daemon daemon died without mounting"
            wait "$pid" 2>/dev/null || true
            return 1
        fi
        if mountpoint -q "$MNT_DIR"; then
            log "  $daemon mounted (pid=$pid)"
            return 0
        fi
        sleep 0.1
    done
    log "  ERROR: $daemon failed to mount"
    kill "$pid" 2>/dev/null || true
    wait "$pid" 2>/dev/null || true
    return 1
}

stop_daemon() {
    if [ -n "${DAEMON_PID:-}" ]; then
        kill "$DAEMON_PID" 2>/dev/null || true
        wait "$DAEMON_PID" 2>/dev/null || true
        # Force unmount if still mounted (the fuser daemon unmounts on
        # drop, the backend one on umount(); a SIGTERM race can leave
        # either behind).
        if mountpoint -q "$MNT_DIR" 2>/dev/null; then
            fusermount3 -u "$MNT_DIR" 2>/dev/null || umount "$MNT_DIR" 2>/dev/null || true
        fi
        DAEMON_PID=""
    fi
}

run_daemon_suite() {
    local daemon=$1 threads=$2

    if [ "$daemon" = "backend" ]; then
        start_backend "$threads" || return 1
    else
        start_fuser "$threads" || return 1
    fi

    # Warm up.
    sleep 1

    # filecreate: metadata-heavy — 5000 small files.
    log -n "  filecreate... "
    run_workload "filecreate" "write" "4k" "4k" "5000" \
        "$RESULTS_DIR/${daemon}_t${threads}_filecreate.json" \
        2>/dev/null || true
    log "done"

    # The data workloads need a test file; create it through the mount so
    # the daemon sees it.
    dd if=/dev/urandom of="$MNT_DIR/testfile" bs=1M count=256 2>/dev/null || true

    # randread-4k
    log -n "  randread-4k... "
    run_multithread_workload "randread-4k" "randread" "4k" "256M" "1" "$threads" \
        "$RESULTS_DIR/${daemon}_t${threads}_randread-4k.json" \
        2>/dev/null || true
    log "done"

    # randwrite-4k
    log -n "  randwrite-4k... "
    run_multithread_workload "randwrite-4k" "randwrite" "4k" "256M" "1" "$threads" \
        "$RESULTS_DIR/${daemon}_t${threads}_randwrite-4k.json" \
        2>/dev/null || true
    log "done"

    # seqread-128k
    log -n "  seqread-128k... "
    run_multithread_workload "seqread-128k" "read" "128k" "256M" "1" "$threads" \
        "$RESULTS_DIR/${daemon}_t${threads}_seqread-128k.json" \
        2>/dev/null || true
    log "done"

    # seqwrite-128k
    log -n "  seqwrite-128k... "
    run_multithread_workload "seqwrite-128k" "write" "128k" "256M" "1" "$threads" \
        "$RESULTS_DIR/${daemon}_t${threads}_seqwrite-128k.json" \
        2>/dev/null || true
    log "done"

    stop_daemon
}

# Main
log "============================================================"
log "  fuse-backend-rs vs fuser Performance Comparison"
log "  $(date)"
log "  Kernel: $(uname -r)"
log "  CPU: $(nproc) cores"
log "  backend: ${BACKEND_BIN} ${BACKEND_EXTRA}"
log "  fuser:   ${FUSER_BIN} ${FUSER_EXTRA}"
log "============================================================"
log ""

rm -rf "$RESULTS_DIR"
mkdir -p "$RESULTS_DIR"

daemon_idx=0
for threads in ${THREADS_LIST}; do
    log "=== Thread count: $threads ==="
    log ""

    # Alternate the daemon order between thread counts to spread runner
    # drift (warmup, thermals) across the two daemons.
    if [ $((daemon_idx % 2)) -eq 0 ]; then
        order=("backend" "fuser")
    else
        order=("fuser" "backend")
    fi
    daemon_idx=$((daemon_idx + 1))

    for daemon in "${order[@]}"; do
        log "--- $daemon ---"
        run_daemon_suite "$daemon" "$threads" || {
            log "  ERROR: $daemon suite failed at $threads threads, skipping"
            stop_daemon
        }
        log ""
    done
done

# Cleanup
rm -rf "$SRC_DIR" "$MNT_DIR"

# Results table on stdout, so CI can append it to the job summary while
# progress lines stay in the log.
python3 "$(dirname "$0")/parse_library_compare.py" "$RESULTS_DIR" ${THREADS_LIST}
