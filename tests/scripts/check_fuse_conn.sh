#!/bin/bash
# Check negotiated FUSE connection parameters for both daemons
set -u
CONN_DIR=/sys/fs/fuse/connections
MNT=/tmp/ft-mnt
SRC=/tmp/ft-src

check_daemon() {
    local name=$1
    shift
    rm -rf "$SRC" "$MNT" && mkdir -p "$SRC" "$MNT"
    local before after conn
    before=$(ls "$CONN_DIR" 2>/dev/null | sort)
    "$@" "$SRC" "$MNT" 2>/dev/null &
    local pid=$!
    sleep 1
    after=$(ls "$CONN_DIR" 2>/dev/null | sort)
    conn=$(comm -13 <(echo "$before") <(echo "$after") | head -1)
    echo "=== $name (conn=$conn) ==="
    if [ -n "$conn" ]; then
        for f in "$CONN_DIR/$conn"/*; do
            [ -f "$f" ] && echo "  $(basename "$f"): $(cat "$f" 2>/dev/null)"
        done
    fi
    kill $pid 2>/dev/null
    wait $pid 2>/dev/null
    fusermount3 -u "$MNT" 2>/dev/null || true
    sleep 0.5
}

check_daemon "fuse-backend-rs" /tmp/fuser-compare/target/release/passthrough
check_daemon "fuser" /tmp/fuser-compare/target/release/passthrough-fuser
