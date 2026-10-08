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

# Unmount a leftover mount at $T/mnt, alive or dead.  Detection scans
# /proc/self/mountinfo instead of stat()-based tools like mountpoint -q:
# a daemon that died without umounting leaves a dead mount whose stat()
# fails with ENOTCONN, so mountpoint -q and [ -e ] are blind to it, and
# the next daemon then rejects the mountpoint as "not a directory".
unmount_leftover_mount() {
    grep -Fqs -- " $T/mnt " /proc/self/mountinfo || return 0
    fusermount -u "$T/mnt" 2>/dev/null \
        || fusermount3 -u "$T/mnt" 2>/dev/null \
        || umount "$T/mnt" 2>/dev/null
}

# A previous crashed run may have left a FUSE mount behind; unmount it
# before removing the scratch dir, so rm does not recurse into it.
unmount_leftover_mount
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

# lower-layer hard links for the deterministic copy-up scenario: reading
# b before the others makes b's link the primary link, and links read
# only after the copy-up stay lower-only entries of the copied-up inode
echo early > "$T/lower/a/early"
ln "$T/lower/a/early" "$T/lower/b/early"
ln "$T/lower/a/early" "$T/lower/c/early"

# lower-layer hard links for the copy-up materialization scenario: both
# link directories are read before the write, so both links are live and
# lower-only when the copy-up happens
echo fresh > "$T/lower/a/fresh"
ln "$T/lower/a/fresh" "$T/lower/b/fresh"

# lower-layer entries for the whiteout-replacement scenarios: unlinking
# an entry recreated over a whiteout must white it out again, which the
# daemon decides from a flag persisted at replacement time instead of
# probing the lower layers on every unlink
echo repl > "$T/lower/a/repl"
echo lnkdata > "$T/lower/b/lnk"
mkdir -p "$T/lower/a/ddir"

# lower-layer entries for the mknod/symlink whiteout-replacement
# scenarios: every node type created over a whiteout must record the
# shadowed lower entry
echo symdata > "$T/lower/a/sym"
echo fifodata > "$T/lower/a/fifo"

# lower-layer directory with children for the recreate-over-rmdir scenario:
# the recreated directory must not expose the old lower children again
mkdir -p "$T/lower/a/resdir"
echo res1 > "$T/lower/a/resdir/res1"
echo res2 > "$T/lower/a/resdir/res2"

# second copy for the variant with a daemon restart between the rmdir
# and the recreate: the layer scan's whiteout flag reconstruction is
# what carries the opaque decision across that restart
mkdir -p "$T/lower/a/resdir2"
echo res1 > "$T/lower/a/resdir2/res1"
echo res2 > "$T/lower/a/resdir2/res2"

# lower-layer entries for the daemon-restart scenarios: the whiteout
# decision flag lives in memory only, so a restart between the
# flag-setting event and the unlink must reconstruct it from the layer
# scan
echo single2 > "$T/lower/a/single2"
echo repl2 > "$T/lower/a/repl2"
echo lnkdata2 > "$T/lower/b/lnk2"

# lower-layer directory for the rmdir-with-whiteout scenario
mkdir -p "$T/lower/e"
echo f1content > "$T/lower/e/f1"

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
    unmount_leftover_mount
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
    # A daemon that crashed mid-run leaves its mount behind (alive or
    # dead); clear it so the next start_daemon can take the mountpoint.
    unmount_leftover_mount
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
echo x >> "$T/mnt/a/d"          # copies the file up; the other live link is materialized with it
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
echo x >> "$T/mnt/a/late1"                          # copy-up: the live links in a are materialized with it
ln "$T/mnt/a/late1" "$T/mnt/a/late4"                # a second upper-layer entry
ls "$T/mnt/c" > /dev/null                           # registers c's link as lower-only
rm "$T/mnt/a/late1"
check "rm one link of the copied-up file" $?
[ "$(cat "$T/mnt/a/late2")" = "$(printf 'late\nx')" ]; check "loaded link sees copied-up data" $?
stop_daemon
start_daemon
[ "$(cat "$T/mnt/c/late3")" = "$(printf 'late\nx')" ]; check "lower-only link serves copied-up data" $?
ls "$T/mnt/c" | grep -qx late3; check "directory listing shows the link's own name" $?
[ "$(stat -c %i "$T/mnt/a/late4")" = "$(stat -c %i "$T/mnt/c/late3")" ]; check "remaining links share the inode" $?
[ ! -e "$T/mnt/a/late1" ]; check "removed link stays gone after remount" $?

echo "== 13. rmdir a directory whose last entry is a whiteout =="
stop_daemon
start_daemon
touch "$T/mnt/e/new"          # copies e up; e/f1 stays a lower-only entry
rm "$T/mnt/e/f1"              # a whiteout placeholder replaces the entry
rm "$T/mnt/e/new"
sleep 1                       # let the kernel settle the unlink forgets
rmdir "$T/mnt/e"
check "rmdir a directory holding only a whiteout" $?
[ ! -e "$T/mnt/e" ]; check "directory is gone" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/e" ]; check "no resurrection after remount" $?

echo "== 14. rm a lower-only link after copy-up landed at the primary link's name =="
stop_daemon
start_daemon
ls "$T/mnt/b" > /dev/null    # b is read first: b's link becomes the primary link
echo x >> "$T/mnt/b/early"   # copy-up lands at the primary link's own name
[ -f "$T/upper/b/early" ]; check "copied up through the primary link" $?
ls "$T/mnt/a" "$T/mnt/c" > /dev/null  # the other links register as lower-only
[ ! -e "$T/upper/a/early" ]; check "late-read links stay lower-only" $?
# Force the kernel to evict its dentry cache where possible (needs
# root) and let the forgets settle: reloading b afterwards scans its
# link as upper-first with nlink 1, so only the first_real_key share
# path keeps it on the live shared inode instead of allocating a
# second overlay inode for the same file.
if [ -w /proc/sys/vm/drop_caches ]; then
    echo 3 > /proc/sys/vm/drop_caches
    sleep 1
    stat "$T/mnt/b/early" > /dev/null
    [ "$(stat -c %i "$T/mnt/b/early")" = "$(stat -c %i "$T/mnt/c/early")" ]
    check "links share one inode across an eviction" $?
fi
rm "$T/mnt/a/early"          # the removed link itself is lower-only
check "rm the lower-only link of the copied-up file" $?
[ -f "$T/upper/c/early" ]; check "lower-only link materialized in upper" $?
[ -c "$T/upper/a/early" ]; check "whiteout created for the removed name" $?
[ "$(cat "$T/mnt/b/early")" = "$(printf 'early\nx')" ]; check "primary link sees copied-up data" $?
stop_daemon
start_daemon
[ "$(cat "$T/mnt/c/early")" = "$(printf 'early\nx')" ]; check "materialized link serves copied-up data after remount" $?
[ "$(cat "$T/mnt/b/early")" = "$(printf 'early\nx')" ]; check "primary link serves copied-up data after remount" $?
[ "$(stat -c %i "$T/mnt/b/early")" = "$(stat -c %i "$T/mnt/c/early")" ]; check "remaining links share the inode after remount" $?
[ ! -e "$T/mnt/a/early" ]; check "removed link stays gone after remount" $?

echo "== 15. copy-up through one link materializes the other links =="
stop_daemon
start_daemon
stat "$T/mnt/a/fresh" "$T/mnt/b/fresh" > /dev/null  # both links live and lower-only
echo x >> "$T/mnt/a/fresh"                          # copy-up through one link
[ -f "$T/upper/a/fresh" ]; check "written link copied up" $?
[ -f "$T/upper/b/fresh" ]; check "other link materialized at copy-up" $?
[ "$(cat "$T/mnt/b/fresh")" = "$(printf 'fresh\nx')" ]; check "other link sees copied-up data" $?
stop_daemon
start_daemon
[ "$(cat "$T/mnt/a/fresh")" = "$(printf 'fresh\nx')" ]; check "written link survives remount" $?
[ "$(cat "$T/mnt/b/fresh")" = "$(printf 'fresh\nx')" ]; check "materialized link serves copied-up data after remount" $?
[ "$(stat -c %i "$T/mnt/a/fresh")" = "$(stat -c %i "$T/mnt/b/fresh")" ]; check "links share the inode after remount" $?
[ "$(stat -c %h "$T/mnt/a/fresh")" = "2" ]; check "nlink stays correct after remount" $?

echo "== 16. unlink a file recreated over a whiteout =="
stop_daemon
start_daemon
rm "$T/mnt/a/repl"                       # whiteout replaces the lower entry
echo replacement > "$T/mnt/a/repl"       # recreate the file over the whiteout
[ "$(cat "$T/mnt/a/repl")" = "replacement" ]; check "recreated file readable" $?
rm "$T/mnt/a/repl"
check "unlink the recreated file" $?
[ -c "$T/upper/a/repl" ]; check "whiteout recreated for the removed name" $?
[ ! -e "$T/mnt/a/repl" ]; check "recreated file is gone" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/a/repl" ]; check "lower entry stays shadowed after remount" $?

echo "== 17. unlink a hard link created over a whiteout =="
stop_daemon
start_daemon
echo src > "$T/mnt/a/src"                # a fresh upper-only file
rm "$T/mnt/b/lnk"                        # whiteout replaces the lower entry
ln "$T/mnt/a/src" "$T/mnt/b/lnk"         # the link replaces the whiteout
[ "$(cat "$T/mnt/b/lnk")" = "src" ]; check "link over whiteout readable" $?
[ "$(stat -c %i "$T/mnt/a/src")" = "$(stat -c %i "$T/mnt/b/lnk")" ]; check "link over whiteout shares inode" $?
rm "$T/mnt/a/src"
check "unlink the source link" $?
[ "$(cat "$T/mnt/b/lnk")" = "src" ]; check "remaining link readable" $?
rm "$T/mnt/b/lnk"
check "unlink the link created over the whiteout" $?
[ -c "$T/upper/b/lnk" ]; check "whiteout recreated for the removed name" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/b/lnk" ]; check "lower entry stays shadowed after remount" $?

echo "== 18. rmdir a directory recreated over a whiteout =="
stop_daemon
start_daemon
rmdir "$T/mnt/a/ddir"                     # whiteout replaces the lower dir
mkdir "$T/mnt/a/ddir"                     # recreate the dir over the whiteout
rmdir "$T/mnt/a/ddir"
check "rmdir the recreated directory" $?
[ -c "$T/upper/a/ddir" ]; check "whiteout recreated for the removed name" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/a/ddir" ]; check "lower dir stays shadowed after remount" $?

echo "== 19. rm a copied-up file after a daemon restart =="
stop_daemon
start_daemon
echo x >> "$T/mnt/a/single2"   # copies the file up and records the shadowed lower entry
[ -f "$T/upper/a/single2" ]; check "single-link file copied up through write" $?
stop_daemon
start_daemon                   # the restart must re-derive the flag from the layer scan
[ "$(cat "$T/mnt/a/single2")" = "$(printf 'single2\nx')" ]; check "copied-up file readable after restart" $?
rm "$T/mnt/a/single2"
check "rm copied-up file after restart" $?
[ -c "$T/upper/a/single2" ]; check "whiteout created for the removed name" $?
[ ! -e "$T/mnt/a/single2" ]; check "removed file is gone" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/a/single2" ]; check "no resurrection after remount" $?

echo "== 20. unlink a file recreated over a whiteout after a daemon restart =="
stop_daemon
start_daemon
rm "$T/mnt/a/repl2"                       # whiteout replaces the lower entry
echo replacement > "$T/mnt/a/repl2"       # recreate the file over the whiteout
[ "$(cat "$T/mnt/a/repl2")" = "replacement" ]; check "recreated file readable" $?
stop_daemon
start_daemon
[ "$(cat "$T/mnt/a/repl2")" = "replacement" ]; check "recreated file readable after restart" $?
rm "$T/mnt/a/repl2"
check "unlink the recreated file after restart" $?
[ -c "$T/upper/a/repl2" ]; check "whiteout recreated for the removed name" $?
[ ! -e "$T/mnt/a/repl2" ]; check "recreated file is gone" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/a/repl2" ]; check "lower entry stays shadowed after remount" $?

echo "== 21. unlink a hard link created over a whiteout after a daemon restart =="
stop_daemon
start_daemon
echo src2 > "$T/mnt/a/src2"               # a fresh upper-only file
rm "$T/mnt/b/lnk2"                        # whiteout replaces the lower entry
ln "$T/mnt/a/src2" "$T/mnt/b/lnk2"        # the link replaces the whiteout
[ "$(cat "$T/mnt/b/lnk2")" = "src2" ]; check "link over whiteout readable" $?
[ "$(stat -c %i "$T/mnt/a/src2")" = "$(stat -c %i "$T/mnt/b/lnk2")" ]; check "link over whiteout shares inode" $?
stop_daemon
start_daemon                              # rebuilds the shared inode from whichever
                                          # name is read first, so the link joining it
                                          # must carry the flag over
[ "$(cat "$T/mnt/a/src2")" = "src2" ]; check "source link readable after restart" $?
[ "$(cat "$T/mnt/b/lnk2")" = "src2" ]; check "link over whiteout readable after restart" $?
[ "$(stat -c %i "$T/mnt/a/src2")" = "$(stat -c %i "$T/mnt/b/lnk2")" ]; check "links share inode after restart" $?
rm "$T/mnt/a/src2"
check "unlink the source link after restart" $?
[ "$(cat "$T/mnt/b/lnk2")" = "src2" ]; check "remaining link readable" $?
rm "$T/mnt/b/lnk2"
check "unlink the link created over the whiteout" $?
[ -c "$T/upper/b/lnk2" ]; check "whiteout recreated for the removed name" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/b/lnk2" ]; check "lower entry stays shadowed after remount" $?

echo "== 22. unlink a symlink recreated over a whiteout after a daemon restart =="
stop_daemon
start_daemon
rm "$T/mnt/a/sym"                        # whiteout replaces the lower entry
ln -s target "$T/mnt/a/sym"              # the symlink replaces the whiteout
[ "$(readlink "$T/mnt/a/sym")" = "target" ]; check "recreated symlink readable" $?
stop_daemon
start_daemon
[ "$(readlink "$T/mnt/a/sym")" = "target" ]; check "recreated symlink readable after restart" $?
rm "$T/mnt/a/sym"
check "unlink the recreated symlink after restart" $?
[ -c "$T/upper/a/sym" ]; check "whiteout recreated for the removed name" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/a/sym" ]; check "lower entry stays shadowed after remount" $?

echo "== 23. unlink a fifo recreated over a whiteout after a daemon restart =="
stop_daemon
start_daemon
rm "$T/mnt/a/fifo"                       # whiteout replaces the lower entry
mkfifo "$T/mnt/a/fifo"                   # the fifo replaces the whiteout
[ -p "$T/mnt/a/fifo" ]; check "recreated fifo exists" $?
stop_daemon
start_daemon
[ -p "$T/mnt/a/fifo" ]; check "recreated fifo exists after restart" $?
rm "$T/mnt/a/fifo"
check "unlink the recreated fifo after restart" $?
[ -c "$T/upper/a/fifo" ]; check "whiteout recreated for the removed name" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/a/fifo" ]; check "lower entry stays shadowed after remount" $?

echo "== 24. children stay gone after rmdir and mkdir over a lower directory =="
stop_daemon
start_daemon
rm "$T/mnt/a/resdir/res1" "$T/mnt/a/resdir/res2"
rmdir "$T/mnt/a/resdir"
check "rmdir the emptied lower directory" $?
mkdir "$T/mnt/a/resdir"
check "recreate the directory over the whiteout" $?
[ "$(ls "$T/mnt/a/resdir" | wc -l)" = "0" ]; check "recreated directory empty in-session" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/a/resdir/res1" ]; check "old lower child stays gone after remount" $?
[ ! -e "$T/mnt/a/resdir/res2" ]; check "second old lower child stays gone after remount" $?
[ "$(ls "$T/mnt/a/resdir" | wc -l)" = "0" ]; check "recreated directory still empty after remount" $?
echo new > "$T/mnt/a/resdir/new"
[ "$(cat "$T/mnt/a/resdir/new")" = "new" ]; check "new child of the recreated directory readable" $?
rm "$T/mnt/a/resdir/new"
check "remove the new child of the recreated directory" $?
rmdir "$T/mnt/a/resdir"
check "rmdir the recreated opaque directory" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/a/resdir" ]; check "recreated opaque directory stays gone after remount" $?

echo "== 25. children stay gone when the directory is recreated after a daemon restart =="
rm "$T/mnt/a/resdir2/res1" "$T/mnt/a/resdir2/res2"
rmdir "$T/mnt/a/resdir2"
check "rmdir the second emptied lower directory" $?
stop_daemon
start_daemon
mkdir "$T/mnt/a/resdir2"
check "recreate the second directory over the scanned whiteout" $?
stop_daemon
start_daemon
[ ! -e "$T/mnt/a/resdir2/res1" ]; check "old lower child of the second directory stays gone after remount" $?
[ ! -e "$T/mnt/a/resdir2/res2" ]; check "second old lower child of the second directory stays gone after remount" $?
[ "$(ls "$T/mnt/a/resdir2" | wc -l)" = "0" ]; check "second recreated directory empty after remount" $?

stop_daemon

if [ "$FAILED" -ne 0 ]; then
    echo "RESULT: FAILED"
    exit 1
fi
echo "RESULT: PASSED"
