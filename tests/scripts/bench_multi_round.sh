#!/bin/bash
# Run the full library-compare benchmark N rounds, each into its own results dir.
set -u
ROUNDS=${1:-3}
SCRIPT="$(cd "$(dirname "$0")" && pwd)/bench_library_compare.sh"
BASE_RESULTS_DIR="${RESULTS_DIR:-fuser-compare-results}"

for r in $(seq 1 "$ROUNDS"); do
    DIR="${BASE_RESULTS_DIR}-r$r"
    echo "################ round $r start: $(date '+%H:%M:%S') ################"
    RESULTS_DIR="$DIR" bash "$SCRIPT"
    echo "################ round $r done:  $(date '+%H:%M:%S') ################"
done
echo "ALL ROUNDS DONE"
