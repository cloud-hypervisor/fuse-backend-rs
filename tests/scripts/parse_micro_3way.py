#!/usr/bin/env python3
"""Aggregate bench_micro_3way.sh results: per-config mean/stddev/min/max."""
import statistics

rows = {}
with open("/tmp/micro-3way-results.txt") as f:
    for line in f:
        parts = line.split()
        if len(parts) != 6:
            continue
        impl, workers, procs, rnd, ops, lat = parts
        try:
            ops, lat = float(ops), float(lat)
        except ValueError:
            continue
        key = (impl, int(workers), int(procs))
        rows.setdefault(key, []).append((ops, lat))

nrounds = max(len(v) for v in rows.values()) if rows else 0
print("rounds collected: %d" % nrounds)

order = [
    ("epoll", 1), ("epoll", 2), ("epoll", 4),
    ("block", 1), ("block", 2), ("block", 4),
    ("fuser", 1), ("fuser", 2), ("fuser", 4), ("fuser-nc", 4),
]
for procs in (1, 4):
    print("\n=== client_procs=%d ===" % procs)
    print("%-14s %10s %8s %10s %10s | %8s %8s" %
          ("impl/workers", "mean", "stddev", "min", "max", "lat_us", "spread%"))
    for impl, workers in order:
        vals = rows.get((impl, workers, procs))
        if not vals:
            continue
        ops = [v[0] for v in vals]
        lat = [v[1] for v in vals]
        m = statistics.mean(ops)
        sd = statistics.stdev(ops) if len(ops) > 1 else 0.0
        lm = statistics.mean(lat)
        spread = (max(ops) - min(ops)) / m * 100
        print("%-7s w=%-5d %10.0f %8.0f %10.0f %10.0f | %8.1f %7.0f%%" %
              (impl, workers, m, sd, min(ops), max(ops), lm, spread))

# pairwise diffs vs the strongest fuser config (4 threads, clone_fd) at 4 clients
print("\n=== diff vs fuser w4 clone_fd (procs=4) ===")
fus = rows.get(("fuser", 4, 4))
if fus:
    fm = statistics.mean([v[0] for v in fus])
    for impl, workers in order:
        if impl == "fuser" and workers == 4:
            continue
        vals = rows.get((impl, workers, 4))
        if not vals:
            continue
        m = statistics.mean([v[0] for v in vals])
        print("  %-8s w=%d: %+.1f%%" % (impl, workers, (m - fm) / fm * 100))
