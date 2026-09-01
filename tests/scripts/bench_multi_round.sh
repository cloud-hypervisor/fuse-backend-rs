#!/bin/bash
# Run the full library-compare benchmark N rounds, each into its own results dir.
set -u
ROUNDS=${1:-3}
SCRIPT=/tmp/fuser-compare/tests/scripts/bench_library_compare.sh

for r in $(seq 1 $ROUNDS); do
    DIR=/tmp/fuser-compare-results-r$r
    mkdir -p "$DIR"
    sed "s|RESULTS_DIR=\"/tmp/fuser-compare-results\"|RESULTS_DIR=\"$DIR\"|" "$SCRIPT" > /tmp/bench_round.sh
    echo "################ round $r start: $(date '+%H:%M:%S') ################"
    bash /tmp/bench_round.sh > /tmp/bench_round_$r.log 2>&1
    echo "################ round $r done:  $(date '+%H:%M:%S') ################"
done
echo "ALL ROUNDS DONE"
