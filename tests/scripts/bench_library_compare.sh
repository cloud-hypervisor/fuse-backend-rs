#!/bin/bash
# Benchmark: fuse-backend-rs vs fuser passthrough filesystems
# Run on oxs-dev only (requires sudo for mount)
set -euo pipefail

BIN_DIR="/tmp/fuser-compare/target/release"
BACKEND_BIN="$BIN_DIR/passthrough"
FUSER_BIN="$BIN_DIR/passthrough-fuser"
RESULTS_DIR="/tmp/fuser-compare-results"
SRC_DIR="/tmp/fuser-compare-src"
MNT_DIR="/tmp/fuser-compare-mnt"

# Threads to test
THREADS_LIST=(1 2 4 8)

# Workloads
run_workload() {
    local name=$1
    local rw=$2
    local bs=$3
    local size=$4
    local nrfiles=$5
    local outfile=$6
    local extra=${7:-}
    
    fio --name="$name" \
        --directory="$MNT_DIR" \
        --rw="$rw" \
        --bs="$bs" \
        --size="$size" \
        --nrfiles="$nrfiles" \
        --numjobs=1 \
        --time_based \
        --runtime=10 \
        --group_reporting \
        --output-format=json \
        --output="$outfile" \
        $extra \
        2>/dev/null
}

run_multithread_workload() {
    local name=$1
    local rw=$2
    local bs=$3
    local size=$4
    local nrfiles=$5
    local numjobs=$6
    local outfile=$7
    local extra=${8:-}
    
    fio --name="$name" \
        --directory="$MNT_DIR" \
        --rw="$rw" \
        --bs="$bs" \
        --size="$size" \
        --nrfiles="$nrfiles" \
        --numjobs="$numjobs" \
        --time_based \
        --runtime=10 \
        --group_reporting \
        --output-format=json \
        --output="$outfile" \
        $extra \
        2>/dev/null
}

# Start/stop daemons
start_backend() {
    local threads=$1
    rm -rf "$SRC_DIR" "$MNT_DIR"
    mkdir -p "$SRC_DIR" "$MNT_DIR"
    $BACKEND_BIN "$SRC_DIR" "$MNT_DIR" "$threads" &
    DAEMON_PID=$!
    # Wait for mount
    for i in $(seq 1 30); do
        if mountpoint -q "$MNT_DIR" 2>/dev/null; then
            echo "  fuse-backend-rs mounted (pid=$DAEMON_PID, threads=$threads)"
            return 0
        fi
        sleep 0.1
    done
    echo "  ERROR: fuse-backend-rs failed to mount"
    kill $DAEMON_PID 2>/dev/null || true
    return 1
}

start_fuser() {
    local threads=$1
    rm -rf "$SRC_DIR" "$MNT_DIR"
    mkdir -p "$SRC_DIR" "$MNT_DIR"
    $FUSER_BIN "$SRC_DIR" "$MNT_DIR" -t "$threads" &
    DAEMON_PID=$!
    # Wait for mount
    for i in $(seq 1 30); do
        if mountpoint -q "$MNT_DIR" 2>/dev/null; then
            echo "  fuser mounted (pid=$DAEMON_PID, threads=$threads)"
            return 0
        fi
        sleep 0.1
    done
    echo "  ERROR: fuser failed to mount"
    kill $DAEMON_PID 2>/dev/null || true
    return 1
}

stop_daemon() {
    if [ -n "${DAEMON_PID:-}" ]; then
        kill $DAEMON_PID 2>/dev/null || true
        wait $DAEMON_PID 2>/dev/null || true
        # Force unmount if still mounted
        if mountpoint -q "$MNT_DIR" 2>/dev/null; then
            fusermount3 -u "$MNT_DIR" 2>/dev/null || sudo umount -f "$MNT_DIR" 2>/dev/null || true
        fi
        DAEMON_PID=""
    fi
}

# Parse JSON result
get_iops() {
    python3 -c "import json,sys; d=json.load(sys.stdin); print(d['jobs'][0]['$1']['iops'])" 2>/dev/null || echo "N/A"
}

get_bw() {
    python3 -c "import json,sys; d=json.load(sys.stdin); print(f\"{d['jobs'][0]['$1']['bw']/1024:.1f}\")" 2>/dev/null || echo "N/A"
}

get_lat() {
    python3 -c "import json,sys; d=json.load(sys.stdin); print(f\"{d['jobs'][0]['$1']['lat_ns']['mean']/1000:.1f}\")" 2>/dev/null || echo "N/A"
}

# Main
echo "============================================================"
echo "  fuse-backend-rs vs fuser Performance Comparison"
echo "  $(date)"
echo "  Kernel: $(uname -r)"
echo "  CPU: $(nproc) cores"
echo "============================================================"
echo ""

rm -rf "$RESULTS_DIR"
mkdir -p "$RESULTS_DIR"

for threads in "${THREADS_LIST[@]}"; do
    echo "=== Thread count: $threads ==="
    echo ""
    
    for daemon in "backend" "fuser"; do
        echo "--- $daemon ---"
        
        if [ "$daemon" = "backend" ]; then
            start_backend "$threads" || continue
        else
            start_fuser "$threads" || continue
        fi
        
        # Warm up
        sleep 1
        
        # filecreate: metadata-heavy — create 5000 small files
        echo -n "  filecreate... "
        run_workload "filecreate" "write" "4k" "4k" "5000" \
            "$RESULTS_DIR/${daemon}_t${threads}_filecreate.json" \
            2>/dev/null || true
        echo "done"
        
        # randread-4k
        echo -n "  randread-4k... "
        # Create a test file THROUGH THE MOUNT so it's visible to the daemon
        dd if=/dev/urandom of="$MNT_DIR/testfile" bs=1M count=256 2>/dev/null || true
        run_multithread_workload "randread-4k" "randread" "4k" "256M" "1" "$threads" \
            "$RESULTS_DIR/${daemon}_t${threads}_randread-4k.json" \
            2>/dev/null || true
        echo "done"
        
        # randwrite-4k
        echo -n "  randwrite-4k... "
        run_multithread_workload "randwrite-4k" "randwrite" "4k" "256M" "1" "$threads" \
            "$RESULTS_DIR/${daemon}_t${threads}_randwrite-4k.json" \
            2>/dev/null || true
        echo "done"
        
        # seqread-128k
        echo -n "  seqread-128k... "
        run_multithread_workload "seqread-128k" "read" "128k" "256M" "1" "$threads" \
            "$RESULTS_DIR/${daemon}_t${threads}_seqread-128k.json" \
            2>/dev/null || true
        echo "done"
        
        # seqwrite-128k
        echo -n "  seqwrite-128k... "
        run_multithread_workload "seqwrite-128k" "write" "128k" "256M" "1" "$threads" \
            "$RESULTS_DIR/${daemon}_t${threads}_seqwrite-128k.json" \
            2>/dev/null || true
        echo "done"
        
        stop_daemon
        echo ""
    done
done

# Cleanup
rm -rf "$SRC_DIR" "$MNT_DIR"

echo ""
echo "============================================================"
echo "  Results Summary"
echo "============================================================"
echo ""

# Generate summary table
python3 << 'PYEOF'
import json
import os
import glob

results_dir = "/tmp/fuser-compare-results"
threads_list = [1, 2, 4, 8]
workloads = ["filecreate", "randread-4k", "randwrite-4k", "seqread-128k", "seqwrite-128k"]

def load_result(daemon, threads, workload):
    path = f"{results_dir}/{daemon}_t{threads}_{workload}.json"
    try:
        with open(path) as f:
            content = f.read()
        # fio may write warnings before the JSON; locate the JSON object start
        idx = content.find('{')
        if idx < 0:
            return None, None, None
        data = json.loads(content[idx:])
        job = data['jobs'][0]
        if job.get('error', 0) != 0:
            return None, None, None
        # For write-only workloads, use 'write'; for read, use 'read'
        if workload in ["randwrite-4k", "seqwrite-128k", "filecreate"]:
            section = 'write'
        else:
            section = 'read'
        iops = job[section]['iops']
        bw_mbps = job[section]['bw'] / 1024
        lat_us = job[section]['lat_ns']['mean'] / 1000
        if iops == 0:
            return None, None, None
        return iops, bw_mbps, lat_us
    except:
        return None, None, None

print(f"{'Workload':<16} {'Threads':>7} | {'backend IOPS':>12} {'fuser IOPS':>12} | {'Diff%':>8}")
print("-" * 72)

for wl in workloads:
    for t in threads_list:
        b_iops, b_bw, b_lat = load_result("backend", t, wl)
        f_iops, f_bw, f_lat = load_result("fuser", t, wl)
        
        if b_iops and f_iops and f_iops > 0:
            diff = ((b_iops - f_iops) / f_iops) * 100
            print(f"{wl:<16} {t:>7} | {b_iops:>12.1f} {f_iops:>12.1f} | {diff:>+7.1f}%")
        else:
            print(f"{wl:<16} {t:>7} | {'N/A':>12} {'N/A':>12} | {'N/A':>8}")

print()
print(f"{'Workload':<16} {'Threads':>7} | {'backend BW(MB/s)':>16} {'fuser BW(MB/s)':>16} | {'Diff%':>8}")
print("-" * 76)

for wl in workloads:
    for t in threads_list:
        b_iops, b_bw, b_lat = load_result("backend", t, wl)
        f_iops, f_bw, f_lat = load_result("fuser", t, wl)
        
        if b_bw and f_bw and f_bw > 0:
            diff = ((b_bw - f_bw) / f_bw) * 100
            print(f"{wl:<16} {t:>7} | {b_bw:>16.1f} {f_bw:>16.1f} | {diff:>+7.1f}%")
        else:
            print(f"{wl:<16} {t:>7} | {'N/A':>16} {'N/A':>16} | {'N/A':>8}")

print()
print(f"{'Workload':<16} {'Threads':>7} | {'backend Lat(us)':>16} {'fuser Lat(us)':>16} | {'Diff%':>8}")
print("-" * 76)

for wl in workloads:
    for t in threads_list:
        b_iops, b_bw, b_lat = load_result("backend", t, wl)
        f_iops, f_bw, f_lat = load_result("fuser", t, wl)
        
        if b_lat and f_lat and f_lat > 0:
            diff = ((b_lat - f_lat) / f_lat) * 100
            print(f"{wl:<16} {t:>7} | {b_lat:>16.1f} {f_lat:>16.1f} | {diff:>+7.1f}%")
        else:
            print(f"{wl:<16} {t:>7} | {'N/A':>16} {'N/A':>16} | {'N/A':>8}")

PYEOF

echo ""
echo "Detailed JSON results saved in: $RESULTS_DIR/"
