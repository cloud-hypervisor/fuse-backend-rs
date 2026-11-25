#!/bin/bash
# Clean create microbenchmark: python in-process loop (no fork/exec per file)
set -u
SRC=/tmp/ft-src
MNT=/tmp/ft-mnt

cat > /tmp/create_bench.py << 'PYEOF'
import os, sys, time
mnt = sys.argv[1]
n = int(sys.argv[2])
start = time.monotonic()
for i in range(n):
    fd = os.open(os.path.join(mnt, "f%d" % i), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    os.close(fd)
elapsed = time.monotonic() - start
print("%.1f us/file (%.2fs for %d files)" % (elapsed * 1e6 / n, elapsed, n))
PYEOF

run_daemon() {
    local label=$1 bin=$2
    shift 2
    for r in 1 2 3; do
        rm -rf "$SRC" "$MNT" && mkdir -p "$SRC" "$MNT"
        "$bin" "$SRC" "$MNT" "$@" 2>/dev/null &
        local pid=$!
        sleep 1
        echo -n "$label round$r: "
        python3 /tmp/create_bench.py "$MNT" 10000
        kill $pid 2>/dev/null
        wait $pid 2>/dev/null
        fusermount3 -u "$MNT" 2>/dev/null || true
        sleep 0.3
    done
}

MODE=${1:-both}
if [ "$MODE" = "backend" ] || [ "$MODE" = "both" ]; then
    run_daemon "backend" /tmp/fuser-compare/target/release/passthrough 1
fi
if [ "$MODE" = "fuser" ] || [ "$MODE" = "both" ]; then
    run_daemon "fuser  " /tmp/fuser-compare/target/release/passthrough-fuser
fi
