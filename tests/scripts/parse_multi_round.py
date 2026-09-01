#!/usr/bin/env python3
"""Aggregate multi-round library-compare results: per-round IOPS + mean + spread."""
import json
import glob

threads_list = [1, 2, 4, 8]
workloads = ["filecreate", "randread-4k", "randwrite-4k", "seqread-128k", "seqwrite-128k"]
WRITE_WORKLOADS = {"randwrite-4k", "seqwrite-128k", "filecreate"}
round_dirs = sorted(glob.glob("/tmp/fuser-compare-results-r*"))
nrounds = len(round_dirs)


def load(rdir, daemon, threads, workload):
    path = "{}/{}_t{}_{}.json".format(rdir, daemon, threads, workload)
    try:
        with open(path) as f:
            content = f.read()
        idx = content.find("{")
        if idx < 0:
            return None
        data = json.loads(content[idx:])
        job = data["jobs"][0]
        if job.get("error", 0) != 0:
            return None
        section = "write" if workload in WRITE_WORKLOADS else "read"
        iops = job[section]["iops"]
        return iops if iops > 0 else None
    except Exception:
        return None


print("rounds: {}".format(nrounds))
for w in workloads:
    print("\n=== {} ===".format(w))
    hdr = "{:>3} |".format("thr")
    for daemon in ("backend", "fuser"):
        hdr += " {:>34} |".format(daemon + " (r1/r2/r3, mean)")
    print(hdr)
    print("-" * len(hdr))
    for t in threads_list:
        row = "{:>3} |".format(t)
        means = {}
        for daemon in ("backend", "fuser"):
            vals = []
            for rdir in round_dirs:
                v = load(rdir, daemon, t, w)
                vals.append(v)
            got = [v for v in vals if v is not None]
            if got:
                m = sum(got) / len(got)
                means[daemon] = m
                spread = (max(got) - min(got)) / m * 100 if len(got) > 1 else 0
                cell = " ".join("{:.0f}".format(v) if v else "-" for v in vals)
                cell += "  m={:.0f} d={:.0f}%".format(m, spread)
                row += " {:>34} |".format(cell)
            else:
                row += " {:>34} |".format("N/A")
        print(row)
    # mean diff
    print("  mean diff% (backend vs fuser) per round:")
    for i, rdir in enumerate(round_dirs):
        parts = []
        for t in threads_list:
            b = load(rdir, "backend", t, w)
            f = load(rdir, "fuser", t, w)
            if b and f:
                parts.append("t{}:{:+.0f}%".format(t, (b - f) / f * 100))
        print("    r{}: {}".format(i + 1, "  ".join(parts)))
