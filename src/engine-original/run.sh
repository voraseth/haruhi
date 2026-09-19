#!/bin/sh
# The ORIGINAL campaign engine (paper: Algorithm 6, linear mode only).
#
# This is one half of reproduction-record row R7a: the 631 linear runs of the
# class elimination were carried by this family of programs and, independently,
# by the engine in ../class-elimination/, which was written from the raw
# definitions with no code in common.  The two agree run for run, node for node.
#
# This engine has NO loop mode.  It was built on an assumption of linear
# closure order that explicitly constructed superpermutations refute, which is
# why the loop-complete search exists at all; see ../cleanroom-loop/README.md
# and row C11 of the paper's conformance ledger.
#
#   realize.c    the (20,0,0) cells, m2spec form
#   realize2.c   + the s2 list and b_{q1}
#   realize3.c   + the nd4 parameter
#   realize4.c   the defect class (15,0,1), both K2 wirings (zh, zp3)
#   realize_check.py   an independent Python cross-checker of the piece algebra
#   run_e9.sh    the eight sub-configurations of the pinned (20,0,0) e=9 census
#   run_e78.sh   the e=8 and e=7 batteries
#   run_z1real.py  the (15,0,1) e=2 battery over both wirings
#   summary.py   totals the committed logs
#   replay_all.py  RE-EXECUTES all 631 jobs and diffs them node-for-node
#
# Committed run logs: CERTIFICATES/campaign-original/realize_*.log
#
#   sh run.sh          build everything and total the committed logs
#   sh run.sh e9       re-run the e=9 battery (~minutes)
#   sh run.sh replay   RE-EXECUTE the whole 631-job campaign and compare it
#                      node-for-node with the committed logs (~15 min on 9
#                      workers; 1.099e10 nodes).  Pass extra args through,
#                      e.g. `sh run.sh replay -j 4`, `sh run.sh replay
#                      --check-only` to validate the job list without running.
#
# NOTE on the default mode.  `sh run.sh` with no argument only *re-tallies* the
# committed logs; on a copy of this tree with those logs removed it prints
# `TOTAL: jobs=0`.  It is a check that the shipped evidence is self-consistent,
# not a re-execution.  Re-execution is `sh run.sh replay`.
set -e
cd "$(dirname "$0")"
for f in realize realize2 realize3 realize4; do cc -O2 -o "$f" "$f.c"; done
if [ "$1" = "e9" ]; then
  sh run_e9.sh
elif [ "$1" = "replay" ]; then
  shift
  python3 replay_all.py "$@"
else
  python3 summary.py
  echo
  echo "expected: every log reports SAT=0 and capped=0, and"
  echo "  TOTAL: jobs=631 nodes=10993460947 SAT=0 capped=0"
  echo "which is the 1.099e10 linear-mode figure of record row R7a."
  echo
  echo "this mode only TOTALS the committed logs.  To RE-EXECUTE all 631 jobs"
  echo "against freshly built binaries and diff them node-for-node, run:"
  echo "  sh run.sh replay"
fi
