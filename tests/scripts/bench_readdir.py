#!/usr/bin/env python3
# Copyright 2026 Alibaba Cloud. All rights reserved.
#
# SPDX-License-Identifier: Apache-2.0
"""Readdir workload: repeated directory enumeration for a fixed time.

fio has no directory-enumeration engine, so bench_sync_async.sh calls this
helper instead: it walks the mountpoint with os.scandir() (getdents64) over
and over, first for a 2 second ramp whose counts are discarded, then for the
requested measurement time. Every enumeration is streamed to the fuse
daemon (the kernel does not serve fuse readdir from its dentry cache), so
the reported rate measures the READDIR/READDIRPLUS handlers of the mounted
file system, with READDIRPLUS negotiated by the benchmark daemon.

The output file uses the fio JSON job shape so that bench_compare.py and
the CI tables treat it like any other fio workload:
    iops      directory entries delivered per second
    bw        approximated reply traffic, KiB/s
    io_bytes  approximated reply traffic, bytes
    runtime   measured window in ms
The byte figures approximate the READDIRPLUS reply size: a fuse dirent
plus its entry attributes is roughly 152 bytes plus the name, and the
kernel may fall back to plain READDIR records (about a third of that)
once its dentry cache is warm, so treat them as an upper bound; the
entries-per-second rate is the meaningful metric.

Usage: bench_readdir.py <mountpoint> <runtime-seconds> <output.json>
"""
import json
import os
import sys
import time

# Ramp phase in seconds, discarded from the measurement like fio ramp_time.
RAMP_SECONDS = 2.0
# sizeof(fuse_entry_out) + sizeof(fuse_dirent) on 64-bit hosts: the size of
# one READDIRPLUS reply entry before the (8-byte padded) name.
DIRENTPLUS_BYTES = 152


def enumerate_once(path):
    """One full getdents64 walk of `path`; returns (entries, name_bytes)."""
    entries = 0
    name_bytes = 0
    with os.scandir(path) as it:
        for entry in it:
            entries += 1
            name_bytes += len(entry.name)
    return entries, name_bytes


def main():
    if len(sys.argv) != 4:
        print("usage: bench_readdir.py <mountpoint> <runtime-seconds> "
              "<output.json>")
        sys.exit(2)
    path, out_path = sys.argv[1], sys.argv[3]
    try:
        runtime = float(sys.argv[2])
    except ValueError:
        print("runtime must be a number of seconds")
        sys.exit(2)
    if runtime <= 0:
        print("runtime must be positive")
        sys.exit(2)

    # Fail loudly instead of reporting a hot zero-entries spin loop: the
    # workload is meant to run after filecreate, when the directory holds
    # ${NRFILES} entries.
    if enumerate_once(path)[0] == 0:
        print("no entries to enumerate under %s" % path)
        sys.exit(1)

    # Warm the daemon and kernel caches so the measurement window covers
    # the steady state, like the fio ramp_time of the data workloads.
    ramp_deadline = time.monotonic() + RAMP_SECONDS
    while time.monotonic() < ramp_deadline:
        enumerate_once(path)

    entries = 0
    reply_bytes = 0
    # The deadline is only checked between walks, so the window may
    # overshoot by at most one enumeration; dividing by the actually
    # elapsed time keeps the reported rate honest.
    start = time.monotonic()
    deadline = start + runtime
    while time.monotonic() < deadline:
        count, name_bytes = enumerate_once(path)
        entries += count
        reply_bytes += count * DIRENTPLUS_BYTES + name_bytes
    elapsed = time.monotonic() - start

    # Same shape as one fio job: the read side carries the work, the write
    # side stays zero, and collect() of bench_compare.py picks the active
    # side by exactly that difference. bw is an integer like fio's so the
    # side-by-side summary of the script stays aligned; iops keeps full
    # precision like fio's.
    job = {
        "jobname": "readdir",
        "read": {
            "io_bytes": reply_bytes,
            "bw": round(reply_bytes / elapsed / 1024.0),
            "iops": entries / elapsed,
            "runtime": int(elapsed * 1000),
        },
        "write": {
            "io_bytes": 0,
            "bw": 0.0,
            "iops": 0.0,
            "runtime": 0,
        },
    }
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump({"jobs": [job]}, f, indent=2)
        f.write("\n")


if __name__ == "__main__":
    main()
