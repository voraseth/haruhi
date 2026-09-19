#!/bin/sh
# Exhaustive first-occurrence ordering search (paper: Algorithm 3, Appendix A.3;
# Lemma 5.6, the e=0 slice at length 871).
#
# Usage:
#   sh run.sh          smoke test: the four instances that close at one node
#   sh run.sh all      all nine instances  (~9.0e11 nodes; days of CPU time)
#   sh run.sh calib873 the POSITIVE CONTROL (~8 min; see below)
#
# The positive control.  This engine's production verdict is "solutions=0", and
# a searcher that can only reject proves nothing by rejecting, so it is also run
# where it MUST accept.  All 96 objects of data/optimal-873/ have e=0, D=0,
# X4=6, and L = 843 + E + S + X4 forces S = 24, so (E,S,X4) = (0,24,6) is
# exactly their habitat: the engine must find exactly 96 orderings there and
# exhaust.  It does.  verify_e0_873.py reconstructs a string from each emitted
# ordering, re-deriving every transition weight from the definition of d, and
# checks that each is a length-873 superpermutation and that the set of 96 is
# the known one up to the relabelling the search takes WLOG.
# Committed transcript: CERTIFICATES/e0-calibration-873.log.
#
# The nine instances are (E,S,X4) = (0,S,28-S) for S = 20..28, since
# L = 843 + e + S + X4 and L = 871 with e = 0 forces S + X4 = 28.
# Committed run logs for all nine are in CERTIFICATES/e0-exhaustion/,
# with a JSON certificate per instance for S = 20..25.  Every log ends
# "solutions=0 ... EXHAUSTED".  Node counts: 1 each for S = 20..23,
# then 85,544,716 / 9,255,738,831 / 108,478,731,066 / 380,195,020,600 /
# 397,221,432,130 for S = 24..28.
set -e
cd "$(dirname "$0")"
cc -O2 -o e9exact e9exact.c
# CAP must exceed the largest committed run: S=27 took 3.80e11 nodes and
# S=28 took 3.97e11, so the former cap of 2e11 could not reproduce them
# (the engine treats the cap as a hard stop and reports NODE_CAP_HIT,
# which certifies nothing).  1e12 gives a wide margin.
CAP=${CAP:-1000000000000}
mkdir -p out
if [ "$1" = "calib873" ]; then
  # the positive control: length 873, e = 0, the 96 known optimal orderings
  mkdir -p out
  ./e9exact 0 24 6 999 0 "$CAP" out/E0_873_S24_X6.txt
  python3 verify_e0_873.py out/E0_873_S24_X6.txt
  exit $?
fi
if [ "$1" = "all" ]; then SEL='^0 (2[0-8])'; else SEL='^0 (2[0-3])'; fi
grep -E "$SEL" jobs-e0-871.txt | while read E S X Z Q TAG; do
  ./e9exact "$E" "$S" "$X" "$Z" "$Q" "$CAP" "out/$TAG.txt" >/dev/null
  tail -1 "out/$TAG.txt" | sed "s|^|$TAG |"
done
echo "expected: every line ends 'solutions=0 ... EXHAUSTED'"
