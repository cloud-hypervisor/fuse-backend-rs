#!/usr/bin/env python3
"""Compare filecreate results: baseline (cred switch on) vs patched (off)."""
import json
import sys

workloads = ["filecreate"]
threads_list = [1, 2, 4, 8]


def load(dirpath, daemon, threads):
    path = "{}/{}_t{}_filecreate.json".format(dirpath, daemon, threads)
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
        iops = job["write"]["iops"]
        lat = job["write"]["lat_ns"]["mean"] / 1000
        if iops == 0:
            return None
        return {"iops": iops, "lat": lat}
    except Exception:
        return None


baseline = "/tmp/fuser-compare-results-baseline"
patched = "/tmp/fuser-compare-results"

hdr = "{:>3} | {:>18} {:>18} | {:>18} {:>18}".format(
    "thr", "backend(base)", "backend(nocred)", "fuser(base)", "fuser(nocred)"
)
print(hdr)
print("-" * len(hdr))
for t in threads_list:
    bb = load(baseline, "backend", t)
    pb = load(patched, "backend", t)
    bf = load(baseline, "fuser", t)
    pf = load(patched, "fuser", t)
    row = "{:>3} |".format(t)
    for r in (bb, pb, bf, pf):
        if r:
            row += " {:>10.1f} {:>6.1f}us |".format(r["iops"], r["lat"])
        else:
            row += " {:>18} |".format("N/A")
    print(row)

print()
print("backend improvement (nocred vs base):")
for t in threads_list:
    b = load(baseline, "backend", t)
    p = load(patched, "backend", t)
    if b and p:
        d = (p["iops"] - b["iops"]) / b["iops"] * 100
        print("  t{}: {:.1f} -> {:.1f} IOPS ({:+.1f}%)".format(t, b["iops"], p["iops"], d))
