#!/bin/bash
# Verify credential-switching overhead on the backend filecreate path:
# create 100 files through the mount, count setresuid/setresgid syscalls.
set -u
SRC=/tmp/ft-src
MNT=/tmp/ft-mnt

rm -rf "$SRC" "$MNT" && mkdir -p "$SRC" "$MNT"
/tmp/fuser-compare/target/release/passthrough "$SRC" "$MNT" 1 2>/dev/null &
PID=$!
sleep 1

strace -f -e trace=setresuid,setresgid,setgroups -o /tmp/strace_cred.log -p $PID &
SPID=$!
sleep 0.2

for i in $(seq 1 100); do
    touch "$MNT/f$i"
done
sleep 0.5
kill $SPID 2>/dev/null
wait $SPID 2>/dev/null

echo "=== 100 file creates through backend mount ==="
echo "setresgid calls: $(grep -c 'setresgid' /tmp/strace_cred.log)"
echo "setresuid calls: $(grep -c 'setresuid' /tmp/strace_cred.log)"
echo "setgroups calls: $(grep -c 'setgroups' /tmp/strace_cred.log)"

kill $PID 2>/dev/null
wait $PID 2>/dev/null
fusermount3 -u "$MNT" 2>/dev/null || true
