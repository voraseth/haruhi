#!/bin/bash
# Production driver: the 480 loop-mode class-elimination runs (Alg. alg:sweep,
# clean-room reimplementation, obligation C11/(O1)).
# Checkpointed: any job already holding a verdict line in logs/VERDICTS.txt is
# skipped, so this script may be relaunched at any time (e.g. after the
# nightly 21:58-05:58 SIGSTOP freeze) and resumes where it stopped.
#   ./run_sweep_decide.sh [workers]
cd "$(dirname "$0")" || exit 1
W=${1:-6}
CAP=${CAP:-4000000000000}
CC=${CC:-cc}
mkdir -p logs; touch logs/VERDICTS.txt
[ -x ./bin_n6c11_decide ] || $CC -O2 -o bin_n6c11_decide src/n6c11_decide.c || exit 1

one() {
  tag=$1; mode=$2; shift 2
  grep -q "^$tag " logs/VERDICTS.txt 2>/dev/null && return 0
  out=$(./bin_n6c11_decide --tag "$tag" --mode "$mode" "$@" --cap $CAP 2>&1); rc=$?
  printf '%s rc=%d\n' "$out" "$rc" >> logs/VERDICTS.txt
  if [ "$rc" = 1 ]; then printf 'SAT!! %s\n' "$out" >> logs/SAT_ALERT.txt; fi
}
export -f one; export CAP

awk -F'\t' '{print $1" "$2" "$3}' data/loopjobs.tsv | \
  xargs -P "$W" -I{} bash -c 'one {}'
echo "SWEEP DONE $(date) remaining=$(( 480 - $(grep -c ' mode=' logs/VERDICTS.txt) ))" >> logs/VERDICTS.txt
