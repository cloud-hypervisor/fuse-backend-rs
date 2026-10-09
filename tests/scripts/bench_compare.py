#!/usr/bin/env python3
# Copyright 2026 Alibaba Cloud. All rights reserved.
#
# SPDX-License-Identifier: Apache-2.0

"""Collect and compare fio benchmark results of fuse-backend-rs.

The benchmark script (tests/scripts/bench_sync_async.sh) stores one fio
JSON file per mode and workload (<results-dir>/<mode>-<workload>.json).
This tool normalizes those files into a single result file, and compares
two result files to detect performance changes, e.g. a pull request run
against the baseline recorded on the bench-results branch.

Usage:
    bench_compare.py collect <results-dir> <mode> <out.json>
    bench_compare.py compare <baseline.json> <current.json>
                             [--threshold PERCENT]

The collected format is:
    {"<workload>": {"bw_kib": float, "iops": float, "runtime_ms": int}}
where the metrics are taken from the read side of the fio job if it
transferred data, otherwise from the write side. `runtime_ms` is only
meaningful for the fixed-amount workloads (filecreate/filedelete).
The readdir workload is not driven by fio but by bench_readdir.py, which
reports entries/s as `iops` in the same JSON job shape.

`compare` prints a markdown table and always exits with 0: shared CI
runners are noisy, so the report is advisory and not a merge gate.
The regression threshold defaults to --threshold for the data workloads,
while the metadata workloads (filecreate/filedelete) use a higher fixed
threshold because they are inherently noisier.
"""

import argparse
import json
import os
import sys

# The metadata workloads fluctuate much more than the data workloads even
# on bare metal (up to ~25% between runs of identical code), so flag them
# with a looser threshold to keep the false-positive rate comparable.
# readdir is a per-entry metadata operation like create/delete (and its
# byte metrics are only approximated reply traffic), so it shares the
# conservative class until bare-metal variance data justifies tightening.
METADATA_WORKLOADS = ("filecreate", "filedelete", "readdir")
METADATA_THRESHOLD = 25.0


def collect(results_dir, mode, out_path):
    """Normalize the fio JSON files of one mode into a single result file."""
    prefix = mode + "-"
    results = {}
    for name in sorted(os.listdir(results_dir)):
        if not name.startswith(prefix) or not name.endswith(".json"):
            continue
        workload = name[len(prefix):-len(".json")]
        with open(os.path.join(results_dir, name), encoding="utf-8") as f:
            data = json.load(f)
        job = data["jobs"][0]
        # Pick the side that actually did the work: the data workloads
        # report on the side selected by --rw, while the filecreate and
        # filedelete engines are only active on one side too. Fall back
        # to comparing iops for engines that transfer no data.
        read, write = job["read"], job["write"]

        def activity(side):
            return (side["io_bytes"], side["iops"])

        side = read if activity(read) >= activity(write) else write
        results[workload] = {
            "bw_kib": side["bw"],
            "iops": side["iops"],
            "runtime_ms": side["runtime"],
        }
    if not results:
        raise RuntimeError(
            "no fio results for mode '%s' in %s" % (mode, results_dir)
        )
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2, sort_keys=True)
        f.write("\n")


def delta(base, cur):
    """Relative change of `cur` against `base`, in percent."""
    if base == 0:
        return 0.0
    return (cur - base) / base * 100.0


def fmt(value):
    if value >= 10000 and value == int(value):
        return format(int(value), ",")
    return "%.4g" % value


def compare(baseline_path, current_path, threshold):
    """Print a markdown table comparing two collected result files."""
    with open(baseline_path, encoding="utf-8") as f:
        baseline = json.load(f)
    with open(current_path, encoding="utf-8") as f:
        current = json.load(f)

    title = os.path.basename(current_path)
    print("### %s (baseline: %s)" % (title, os.path.basename(baseline_path)))
    print()
    print("| workload | metric | baseline | current | delta | |")
    print("| --- | --- | ---: | ---: | ---: | --- |")
    for workload in sorted(set(baseline) | set(current)):
        base = baseline.get(workload)
        cur = current.get(workload)
        if base is None or cur is None:
            print("| %s | - | - | - | - | MISSING |" % workload)
            continue
        for metric in ("bw_kib", "iops"):
            d = delta(base[metric], cur[metric])
            # For the fixed-amount metadata workloads a lower bandwidth or
            # IOPS means the same amount of work took longer, which is the
            # interesting signal; runtime is reported for reference only.
            limit = threshold
            if workload in METADATA_WORKLOADS:
                limit = max(threshold, METADATA_THRESHOLD)
            flag = "REGRESSION" if d < -limit else ""
            label = "BW(KiB/s)" if metric == "bw_kib" else "IOPS"
            print(
                "| %s | %s | %s | %s | %+.1f%% | %s |"
                % (workload, label, fmt(base[metric]), fmt(cur[metric]), d, flag)
            )
        if base["runtime_ms"] > 0 and cur["runtime_ms"] > 0:
            d = delta(base["runtime_ms"], cur["runtime_ms"])
            print(
                "| %s | runtime(ms) | %s | %s | %+.1f%% | |"
                % (workload, fmt(base["runtime_ms"]), fmt(cur["runtime_ms"]), d)
            )
    print()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    # No `required=True` here, it is only supported by Python >= 3.7 and
    # the script is meant to run on bare metal machines with whatever
    # python3 is available.
    sub = parser.add_subparsers(dest="cmd")

    p_collect = sub.add_parser("collect", help="normalize fio JSON results")
    p_collect.add_argument("results_dir", help="directory with <mode>-<workload>.json files")
    p_collect.add_argument("mode", help="mode to collect, e.g. sync or async")
    p_collect.add_argument("out", help="output file")

    p_compare = sub.add_parser("compare", help="compare two collected result files")
    p_compare.add_argument("baseline", help="baseline result file")
    p_compare.add_argument("current", help="result file to evaluate")
    p_compare.add_argument(
        "--threshold",
        type=float,
        default=10.0,
        help="flag regressions of the data workloads beyond this percent; "
        "the metadata workloads use at least %.0f%% (default: %%(default)s)"
        % METADATA_THRESHOLD,
    )

    args = parser.parse_args()
    if args.cmd is None:
        parser.print_usage(sys.stderr)
        return 2
    if args.cmd == "collect":
        collect(args.results_dir, args.mode, args.out)
    else:
        compare(args.baseline, args.current, args.threshold)


if __name__ == "__main__":
    sys.exit(main())
