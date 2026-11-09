#!/usr/bin/env python3
"""Parse fio JSON results from the fuse-backend-rs vs fuser comparison."""
import json
import sys

results_dir = sys.argv[1] if len(sys.argv) > 1 else "fuser-compare-results"
# Optional: the thread counts that were run (must match THREADS_LIST given
# to bench_library_compare.sh). Default to the historical local matrix.
threads_list = [int(t) for t in sys.argv[2].split()] if len(sys.argv) > 2 else [1, 2, 4, 8]
workloads = ["filecreate", "randread-4k", "randwrite-4k", "seqread-128k", "seqwrite-128k"]
WRITE_WORKLOADS = {"randwrite-4k", "seqwrite-128k", "filecreate"}


def load_result(daemon, threads, workload):
    path = "{}/{}_t{}_{}.json".format(results_dir, daemon, threads, workload)
    try:
        with open(path) as f:
            content = f.read()
        # fio may prepend warnings before the JSON payload
        idx = content.find("{")
        if idx < 0:
            return None
        data = json.loads(content[idx:])
        job = data["jobs"][0]
        if job.get("error", 0) != 0:
            return None
        section = "write" if workload in WRITE_WORKLOADS else "read"
        iops = job[section]["iops"]
        bw = job[section]["bw"] / 1024
        lat = job[section]["lat_ns"]["mean"] / 1000
        if iops == 0:
            return None
        return {"iops": iops, "bw": bw, "lat": lat}
    except Exception:
        return None


hdr = "{:<14} {:>2} {:>14} {:>12} {:>8} {:>16} {:>14}".format(
    "workload", "thr", "backend IOPS", "fuser IOPS", "diff%", "backend lat(us)", "fuser lat(us)"
)
print(hdr)
print("-" * len(hdr))
for w in workloads:
    for t in threads_list:
        b = load_result("backend", t, w)
        f = load_result("fuser", t, w)
        if b and f:
            diff = (b["iops"] - f["iops"]) / f["iops"] * 100
            print(
                "{:<14} {:>2} {:>14,.0f} {:>12,.0f} {:>7.1f}% {:>16.1f} {:>14.1f}".format(
                    w, t, b["iops"], f["iops"], diff, b["lat"], f["lat"]
                )
            )
        else:
            bv = "{:,.1f}".format(b["iops"]) if b else "N/A"
            fv = "{:,.1f}".format(f["iops"]) if f else "N/A"
            print("{:<14} {:>2} backend={} fuser={}".format(w, t, bv, fv))
