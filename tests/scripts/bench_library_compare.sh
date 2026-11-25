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
# Two scenarios are supported (MODES, default "common"):
#   common  The request/response mode both libraries share: the backend
#           daemon's classic multi-threaded sync workers vs fuser's
#           multi-threaded event loops with clone_fd. This is the only
#           apples-to-apples common denominator, so it is the mode to
#           watch for per-request service-path drift between the libs.
#   best    Each library's strongest transport. fuser has nothing beyond
#           clone_fd multi-threading (already its best); the backend side
#           runs the FUSE-over-io_uring transport when the kernel accepts
#           it (6.14+ with the fuse module parameter enable_uring turned
#           on, off by default on several distro kernels) and falls back
#           to the multi-worker async transport otherwise or when the
#           daemon dies at INIT. This scenario shows the structural gap
#           between the two libraries' architectures, not lib drift.
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
#   MODES          space-separated scenarios, "common" and/or "best"
#                  (default "common")
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
MODES="${MODES:-common}"
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

# kernel_at_least MAJOR MINOR: true if the running kernel is at least
# MAJOR.MINOR. Used to gate the best scenario's uring transport, which
# requires the kernel FUSE_URING interface (6.14+).
kernel_at_least() {
    local want_major=$1 want_minor=$2 kv major minor
    kv=$(uname -r)
    major=${kv%%.*}
    minor=${kv#*.}
    minor=${minor%%.*}
    case "${major}${minor}" in
        *[!0-9]* | "") return 1 ;;
    esac
    [ "${major}" -gt "${want_major}" ] && return 0
    [ "${major}" -eq "${want_major}" ] && [ "${minor}" -ge "${want_minor}" ]
}

# mounted: true if MNT_DIR has a fuse mount entry. mountpoint(1) cannot
# be used for this: on a stale fuse mount ("Transport endpoint is not
# connected") its stat fails and it reports NOT mounted, so the leftover
# would sail past every mountpoint -q check.
mounted() {
    grep -q " ${MNT_DIR} " /proc/mounts
}

# prepare_mountpoint: make sure MNT_DIR is a plain empty directory. A
# daemon that died between mounting and teardown can leave a stale FUSE
# mount behind ("Transport endpoint is not connected"), which makes the
# rm -rf below fail and every later mount fail with EEXIST, poisoning
# the rest of the run; clear such leftovers first so one flaky teardown
# cannot waste the whole matrix. The clear is retried for a few seconds:
# when the previous daemon was just killed, fusermount3's auto_unmount
# helper may still be tearing the mount down and a single immediate
# attempt loses that race.
prepare_mountpoint() {
    local i
    for i in 1 2 3 4 5 6; do
        mounted || break
        fusermount3 -u "$MNT_DIR" 2>/dev/null \
            || fusermount3 -uz "$MNT_DIR" 2>/dev/null \
            || umount "$MNT_DIR" 2>/dev/null \
            || true
        sleep 0.5
    done
    rm -rf "$SRC_DIR" "$MNT_DIR" 2>/dev/null || true
    mkdir -p "$SRC_DIR" "$MNT_DIR"
}

# start_backend <threads> [flags]: the tests/benchmark daemon with the
# writeback cache off, so the write path matches fuser's (which cannot
# negotiate FUSE_WRITEBACK_CACHE). The daemon's stdout/stderr go to a log
# file under RESULTS_DIR, not to this script's streams: the results table
# is printed on stdout, and a child inheriting it would interleave its log
# lines into the table.
start_backend() {
    local threads=$1 flags=${2:-}
    prepare_mountpoint
    # shellcheck disable=SC2086
    "$BACKEND_BIN" "$SRC_DIR" "$MNT_DIR" --no-writeback --threads "$threads" $flags $BACKEND_EXTRA \
        > "$RESULTS_DIR/backend.log" 2>&1 &
    DAEMON_PID=$!
    wait_for_mount "fuse-backend-rs" "$DAEMON_PID"
}

# start_backend_for_mode <threads> <mode>: start the backend daemon with
# the transport the scenario calls for. In the best scenario a resolved
# --uring transport can still be rejected by the kernel at INIT (several
# distro kernels ship it off by default); rather than skipping the whole
# scenario, fall back to the async transport, which is the best this crate
# has on such kernels, and remember the downgrade for the parser header.
start_backend_for_mode() {
    local threads=$1 mode=$2
    if [ "$mode" != "best" ]; then
        start_backend "$threads" ""
        return
    fi
    if start_backend "$threads" "$BEST_FLAGS"; then
        return 0
    fi
    if [ "$BEST_FLAGS" != "--uring" ]; then
        return 1
    fi
    log "  warning: the kernel rejected FUSE-over-io_uring at INIT, falling back to --async"
    BEST_FLAGS="--async"
    printf '%s\n' async > "$RESULTS_DIR/best-mode.txt"
    # Drop a possibly stale mount left by the failed daemon.
    fusermount3 -u "$MNT_DIR" 2>/dev/null || umount "$MNT_DIR" 2>/dev/null || true
    start_backend "$threads" "$BEST_FLAGS"
}

start_fuser() {
    local threads=$1
    prepare_mountpoint
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
        # either behind — as a stale "Transport endpoint is not
        # connected" entry, which mountpoint(1) cannot even see, hence
        # the /proc/mounts check).
        if mounted; then
            fusermount3 -u "$MNT_DIR" 2>/dev/null \
                || fusermount3 -uz "$MNT_DIR" 2>/dev/null \
                || umount "$MNT_DIR" 2>/dev/null || true
        fi
        DAEMON_PID=""
    fi
}

run_daemon_suite() {
    local daemon=$1 threads=$2 mode=$3

    if [ "$daemon" = "backend" ]; then
        start_backend_for_mode "$threads" "$mode" || return 1
    else
        start_fuser "$threads" || return 1
    fi

    # Warm up.
    sleep 1

    # filecreate: metadata-heavy — 5000 small files.
    log -n "  filecreate... "
    run_workload "filecreate" "write" "4k" "4k" "5000" \
        "$RESULTS_DIR/${daemon}_${mode}_t${threads}_filecreate.json" \
        2>/dev/null || true
    log "done"

    # The data workloads need a test file; create it through the mount so
    # the daemon sees it.
    dd if=/dev/urandom of="$MNT_DIR/testfile" bs=1M count=256 2>/dev/null || true

    # randread-4k
    log -n "  randread-4k... "
    run_multithread_workload "randread-4k" "randread" "4k" "256M" "1" "$threads" \
        "$RESULTS_DIR/${daemon}_${mode}_t${threads}_randread-4k.json" \
        2>/dev/null || true
    log "done"

    # randwrite-4k
    log -n "  randwrite-4k... "
    run_multithread_workload "randwrite-4k" "randwrite" "4k" "256M" "1" "$threads" \
        "$RESULTS_DIR/${daemon}_${mode}_t${threads}_randwrite-4k.json" \
        2>/dev/null || true
    log "done"

    # seqread-128k
    log -n "  seqread-128k... "
    run_multithread_workload "seqread-128k" "read" "128k" "256M" "1" "$threads" \
        "$RESULTS_DIR/${daemon}_${mode}_t${threads}_seqread-128k.json" \
        2>/dev/null || true
    log "done"

    # seqwrite-128k
    log -n "  seqwrite-128k... "
    run_multithread_workload "seqwrite-128k" "write" "128k" "256M" "1" "$threads" \
        "$RESULTS_DIR/${daemon}_${mode}_t${threads}_seqwrite-128k.json" \
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
log "  scenarios: ${MODES}"
log "============================================================"
log ""

rm -rf "$RESULTS_DIR"
mkdir -p "$RESULTS_DIR"

# Resolve the backend transport for the best scenario once per run: the
# FUSE-over-io_uring transport needs kernel 6.14+ with the fuse module
# parameter enable_uring turned on (off by default on several distro
# kernels; best effort, a no-op without root or when the parameter does
# not exist). Elsewhere the multi-worker async transport is the best this
# crate has. The startup probe in start_backend_for_mode still handles a
# kernel that keeps rejecting uring at INIT.
BEST_FLAGS="--async"
if kernel_at_least 6 14 && [ -e /sys/module/fuse/parameters/enable_uring ]; then
    ( echo 1 > /sys/module/fuse/parameters/enable_uring ) 2>/dev/null || true
    BEST_FLAGS="--uring"
fi
case " ${MODES} " in
    *" best "*)
        printf '%s\n' "${BEST_FLAGS#--}" > "$RESULTS_DIR/best-mode.txt"
        log "best scenario backend transport: ${BEST_FLAGS}"
        ;;
esac

daemon_idx=0
for mode in ${MODES}; do
    for threads in ${THREADS_LIST}; do
        log "=== Scenario: ${mode}, thread count: ${threads} ==="
        log ""

        # Alternate the daemon order between cells to spread runner drift
        # (warmup, thermals) across the two daemons.
        if [ $((daemon_idx % 2)) -eq 0 ]; then
            order=("backend" "fuser")
        else
            order=("fuser" "backend")
        fi
        daemon_idx=$((daemon_idx + 1))

        for daemon in "${order[@]}"; do
            log "--- $daemon ---"
            run_daemon_suite "$daemon" "$threads" "$mode" || {
                log "  ERROR: $daemon suite failed (scenario $mode, $threads threads), skipping"
                stop_daemon
            }
            log ""
        done
    done
done

# Cleanup. The rm must not abort the script before the table is printed:
# a leftover mount (one the best-effort clears above could not remove)
# makes rm -rf fail with "Is a directory"/EBUSY.
rm -rf "$SRC_DIR" "$MNT_DIR" 2>/dev/null || true

# Results table on stdout, so CI can append it to the job summary while
# progress lines stay in the log. THREADS_LIST and MODES are passed as
# single quoted arguments: unquoted they would word-split into separate
# argv entries and the parser would take the second thread count for a
# scenario name (and vice versa).
python3 "$(dirname "$0")/parse_library_compare.py" "$RESULTS_DIR" "${THREADS_LIST}" "${MODES}"
