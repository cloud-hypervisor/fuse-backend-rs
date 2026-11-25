#!/usr/bin/env python3
"""Parse fio JSON results from the fuse-backend-rs vs fuser comparison."""
import json
import os
import sys

results_dir = sys.argv[1] if len(sys.argv) > 1 else "fuser-compare-results"
# Optional: the thread counts that were run (must match THREADS_LIST given
# to bench_library_compare.sh). Default to the historical local matrix.
threads_list = [int(t) for t in sys.argv[2].split()] if len(sys.argv) > 2 else [1, 2, 4, 8]
# Optional: the scenarios that were run (must match MODES given to
# bench_library_compare.sh). Default to the single-scenario runs that
# predate the MODES knob.
modes_list = sys.argv[3].split() if len(sys.argv) > 3 else ["common"]
workloads = ["filecreate", "randread-4k", "randwrite-4k", "seqread-128k", "seqwrite-128k"]
WRITE_WORKLOADS = {"randwrite-4k", "seqwrite-128k", "filecreate"}

SCENARIO_TITLES = {
    "common": (
        "Scenario 'common' — the request/response mode both libraries share\n"
        "(fuse-backend-rs sync workers vs fuser event loops with clone_fd).\n"
        "Watch this one for per-request service-path drift between the libs."
    ),
    "best": (
        "Scenario 'best' — each library's strongest transport\n"
        "(fuse-backend-rs best transport, fuser clone_fd multi-threading).\n"
        "This one shows the structural gap between the architectures."
    ),
}


def best_transport():
    """The transport the bench script resolved for the best scenario.

    Written to best-mode.txt by bench_library_compare.sh: "uring" or
    "async" (the fallback when the kernel rejects FUSE-over-io_uring).
    """
    try:
        with open(os.path.join(results_dir, "best-mode.txt")) as f:
            return f.read().strip() or None
    except OSError:
        return None


def load_result(daemon, mode, threads, workload):
    path = os.path.join(
        results_dir, "{}_{}_t{}_{}.json".format(daemon, mode, threads, workload)
    )
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

for mode in modes_list:
    title = SCENARIO_TITLES.get(mode, "Scenario '{}'".format(mode))
    if mode == "best":
        transport = best_transport()
        if transport:
            title += "\nBackend best transport this run: --{}.".format(transport)
    print(title)
    print()
    print(hdr)
    print("-" * len(hdr))
    for w in workloads:
        for t in threads_list:
            b = load_result("backend", mode, t, w)
            f = load_result("fuser", mode, t, w)
            if b and f:
                diff = (b["iops"] - f["iops"]) / f["iops"] * 100
                print(
                    "{:<14} {:>2} {:>14,.0f} {:>12,.0f} {:>7.1f}% {:>16.1f} {:>14.1f}".format(
                        w, t, b["iops"], f["iops"], diff, b["lat"], f["lat"]
                    )
                )
            elif b or f:
                bv = "{:,.1f}".format(b["iops"]) if b else "N/A"
                fv = "{:,.1f}".format(f["iops"]) if f else "N/A"
                print("{:<14} {:>2} backend={} fuser={}".format(w, t, bv, fv))
    print()
