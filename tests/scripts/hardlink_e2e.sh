#!/bin/bash
# End-to-end validation of overlayfs hard link semantics, covering
# issue #210 (all links of a file must share one overlay inode) and the
# whiteout/forget handling around it.
#
# Unlike the unionmount suite this can run without root on hosts that
# allow unprivileged FUSE mounts with allow_other (user_allow_other in
# /etc/fuse.conf) and unprivileged whiteout creation (0/0 char device
# mknod); run it under sudo elsewhere.  It also covers daemon restarts,
# which is where whiteout mistakes surface as resurrected lower-layer
# entries.
#
# Usage: tests/scripts/hardlink_e2e.sh [path-to-overlay-binary]
#
# Run on a filesystem supporting user.* xattrs (ext4, xfs, ...): the
# layers probe "user.fuseoverlayfs.opaque" at startup and tmpfs answers
# that probe with EOPNOTSUPP.  The default scratch dir therefore lives
# under $HOME, not /tmp.

set -u
BIN=${1:-$(dirname "$(realpath "$0")")/../../target/debug/overlay}
T=${OVL_HARDLINK_TEST_DIR:-$HOME/ovl-hardlink-e2e}

if [ ! -x "$BIN" ]; then
    echo "overlay binary not found at $BIN (build it with: cargo build -p overlay)" >&2
    exit 1
fi

# A previous crashed run may have left a FUSE mount behind; unmount it
# before removing the scratch dir, so rm does not recurse into it.
if mountpoint -q "$T/mnt" 2>/dev/null; then
    fusermount -u "$T/mnt"
fi
rm -rf "$T"
mkdir -p "$T/lower/a" "$T/lower/b" "$T/lower/c" "$T/upper" "$T/work" "$T/mnt"

# lower-layer hard links
echo hello > "$T/lower/a/f"
ln "$T/lower/a/f" "$T/lower/b/f"

# lower-layer hard links for the copy-up scenario
echo copy > "$T/lower/a/c"
ln "$T/lower/a/c" "$T/lower/b/c"

# lower-layer hard links for the last-upper-entry removal scenario
echo data > "$T/lower/a/d"
ln "$T/lower/a/d" "$T/lower/b/d"

# single-link lower file for the copied-up removal scenario
echo single > "$T/lower/a/single"

# lower-layer hard links for the materialization scenario: the third
# link's directory is read only after the file was copied up
echo late > "$T/lower/a/late1"
ln "$T/lower/a/late1" "$T/lower/a/late2"
ln "$T/lower/a/late1" "$T/lower/c/late3"

FAILED=0
DPID=
check() { # check <description> <condition-result>
    if [ "$2" = "0" ]; then
        echo "PASS: $1"
    else
        echo "FAIL: $1"
        FAILED=1
    fi
}

# Always tear down the daemon, the mount and the scratch dir, however
# the script exits (including start_daemon's exit 1 on start failure).
cleanup() {
    if [ -n "$DPID" ]; then
        kill -TERM "$DPID" 2>/dev/null
        wait "$DPID" 2>/dev/null
        sleep 0.5
    fi
    if mountpoint -q "$T/mnt" 2>/dev/null; then
        fusermount -u "$T/mnt" 2>/dev/null
    fi
    rm -rf "$T"
}
trap cleanup EXIT

start_daemon() {
    nohup "$BIN" -o "lowerdir=$T/lower,upperdir=$T/upper,workdir=$T/work" ovltest "$T/mnt" > "$T/daemon.log" 2>&1 &
    DPID=$!
    for _ in $(seq 1 20); do
        mountpoint -q "$T/mnt" && return 0
        sleep 0.5
    done
    echo "daemon failed to start:" >&2
    cat "$T/daemon.log" >&2
    exit 1
}
stop_daemon() {
    kill -TERM "$DPID" 2>/dev/null
    wait "$DPID" 2>/dev/null
    DPID=
    sleep 0.5
}

start_daemon

echo "== 1. lower hard links share one overlay inode (issue #210) =="
i1=$(stat -c %i "$T/mnt/a/f"); i2=$(stat -c %i "$T/mnt/b/f")
echo "   ino a/f=$i1 b/f=$i2 nlink=$(stat -c %h "$T/mnt/a/f")"
[ "$i1" = "$i2" ] && [ "$(stat -c %h "$T/mnt/a/f")" = "2" ]
check "lower links share one inode and nlink" $?

echo "== 2. rm one lower link; other survives =="
rm "$T/mnt/b/f"
check "unlink one lower link" $?
[ "$(cat "$T/mnt/a/f")" = "hello" ]; check "remaining link readable" $?
[ ! -e "$T/mnt/b/f" ]; check "removed name is gone" $?

echo "== 3. remount: removed lower link must NOT resurrect =="
stop_daemon
start_daemon
[ ! -e "$T/mnt/b/f" ]; check "no resurrection after remount" $?
[ "$(cat "$T/mnt/a/f")" = "hello" ]; check "remaining link survives remount" $?

echo "== 4. upper link creation shares inode =="
echo world > "$T/mnt/a/g"
ln "$T/mnt/a/g" "$T/mnt/b/g"
j1=$(stat -c %i "$T/mnt/a/g"); j2=$(stat -c %i "$T/mnt/b/g")
echo "   ino a/g=$j1 b/g=$j2"
[ "$j1" = "$j2" ]; check "upper links share one inode" $?
echo more >> "$T/mnt/b/g"
[ "$(cat "$T/mnt/a/g")" = "$(printf 'world\nmore')" ]; check "write through one link visible via the other" $?

echo "== 5. rm one upper link; other survives; no resurrection =="
rm "$T/mnt/b/g"
[ "$(cat "$T/mnt/a/g")" = "$(printf 'world\nmore')" ]; check "remaining link readable" $?
stop_daemon
start_daemon
[ "$(cat "$T/mnt/a/g")" = "$(printf 'world\nmore')" ]; check "remaining link survives remount" $?
[ ! -e "$T/mnt/b/g" ]; check "no resurrection after remount" $?

echo "== 6. rm last link; file fully gone =="
rm "$T/mnt/a/g"
[ ! -e "$T/mnt/a/g" ]; check "last link removed" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/a/g" ]; check "file gone after remount" $?

echo "== 7. rm primary link first; extra link survives =="
echo p > "$T/mnt/a/h"
ln "$T/mnt/a/h" "$T/mnt/b/h"
rm "$T/mnt/a/h"
# Force the kernel to evict its dentry cache where possible (needs
# root) and let the forgets settle, so the multi-linked inode is
# forgotten while a link remains: the daemon must keep the shared
# node cached and re-serve it.
if [ -w /proc/sys/vm/drop_caches ]; then
    echo 3 > /proc/sys/vm/drop_caches
    sleep 1
fi
[ ! -e "$T/mnt/a/h" ]; check "primary link removed" $?
[ "$(cat "$T/mnt/b/h")" = "p" ]; check "extra link readable" $?
echo q >> "$T/mnt/b/h"
stop_daemon
start_daemon
[ "$(cat "$T/mnt/b/h")" = "$(printf 'p\nq')" ]; check "extra link survives remount" $?

echo "== 8. link over a whiteout replaces it =="
echo k > "$T/mnt/a/k"
ln "$T/mnt/a/k" "$T/mnt/b/f"   # b/f was whiteout-ed in scenario 2
[ "$(cat "$T/mnt/b/f")" = "k" ]; check "whiteout replaced by link" $?
k1=$(stat -c %i "$T/mnt/a/k"); k2=$(stat -c %i "$T/mnt/b/f")
[ "$k1" = "$k2" ]; check "link over whiteout shares inode" $?
stop_daemon
start_daemon
[ "$(cat "$T/mnt/b/f")" = "k" ]; check "link over whiteout survives remount" $?
[ "$(cat "$T/mnt/a/f")" = "hello" ]; check "original lower file intact" $?
rm "$T/mnt/b/f" "$T/mnt/a/k"

echo "== 9. rm lower-only link after copy-up through the other link =="
stop_daemon
start_daemon
echo x >> "$T/mnt/a/c"   # copies a/c up; b/c stays a lower-only entry
[ -f "$T/upper/a/c" ]; check "link copied up through write" $?
rm "$T/mnt/b/c"
check "rm lower-only link of a copied-up file" $?
[ ! -e "$T/mnt/b/c" ]; check "removed link is gone" $?
[ -c "$T/upper/b/c" ]; check "whiteout created for the removed name" $?
[ "$(cat "$T/mnt/a/c")" = "$(printf 'copy\nx')" ]; check "copied-up link intact" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/b/c" ]; check "no resurrection after remount" $?
[ "$(cat "$T/mnt/a/c")" = "$(printf 'copy\nx')" ]; check "copied-up link survives remount" $?
rm "$T/mnt/a/c"

echo "== 10. rm the copied-up link; remaining link keeps the data =="
stat "$T/mnt/b/d" > /dev/null   # make sure b/d is loaded and shares the inode
echo x >> "$T/mnt/a/d"          # copies a/d up; b/d stays a lower-only entry
rm "$T/mnt/a/d"
check "rm copied-up link while a lower link remains" $?
[ "$(cat "$T/mnt/b/d")" = "$(printf 'data\nx')" ]; check "remaining link sees copied-up data" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/a/d" ]; check "no resurrection after remount" $?
[ "$(cat "$T/mnt/b/d")" = "$(printf 'data\nx')" ]; check "copied-up data survives remount" $?

echo "== 11. rm a copied-up single-link file; whiteout must shadow the lower entry =="
echo x >> "$T/mnt/a/single"   # copies the file up
[ -f "$T/upper/a/single" ]; check "single-link file copied up through write" $?
rm "$T/mnt/a/single"
check "rm copied-up single-link file" $?
[ -c "$T/upper/a/single" ]; check "whiteout created for the removed name" $?
[ ! -e "$T/mnt/a/single" ]; check "removed file is gone" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/a/single" ]; check "no resurrection after remount" $?

echo "== 12. unlink materializes lower-only links of a copied-up file =="
stop_daemon
start_daemon
stat "$T/mnt/a/late1" "$T/mnt/a/late2" > /dev/null  # load a; c stays unread
echo x >> "$T/mnt/a/late1"                          # copy-up: only this entry goes upper
ln "$T/mnt/a/late1" "$T/mnt/a/late4"                # a second upper-layer entry
ls "$T/mnt/c" > /dev/null                           # registers c's link as lower-only
rm "$T/mnt/a/late1"
check "rm one link of the copied-up file" $?
[ "$(cat "$T/mnt/a/late2")" = "$(printf 'late\nx')" ]; check "loaded link sees copied-up data" $?
stop_daemon
start_daemon
[ "$(cat "$T/mnt/c/late3")" = "$(printf 'late\nx')" ]; check "lower-only link serves copied-up data" $?
[ "$(stat -c %i "$T/mnt/a/late4")" = "$(stat -c %i "$T/mnt/c/late3")" ]; check "remaining links share the inode" $?
[ ! -e "$T/mnt/a/late1" ]; check "removed link stays gone after remount" $?

stop_daemon

if [ "$FAILED" -ne 0 ]; then
    echo "RESULT: FAILED"
    exit 1
fi
echo "RESULT: PASSED"
