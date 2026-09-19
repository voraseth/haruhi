#!/bin/sh
# Runs the four post-review audit checkers (paper Appendix C).
# Expected: 97/97 objects pass everywhere; min t = 24; survivor cells identical.
# Exits non-zero if any checker does.  The checkers refuse to run under
# -O / PYTHONOPTIMIZE, which would remove the asserts that carry their checks.
set -e
d=$(dirname "$0")
# run a checker, show the requested tail, and propagate ITS exit status
# (a pipeline would report the exit status of `tail`, not of the checker)
run() { n=$1; shift; out=$("$@") || { printf '%s\n' "$out"; exit 1; }
        printf '%s\n' "$out" | tail -n "$n"; }
echo "== A: base-bound inequalities (i)-(vi), 97 controls =="
run 1 python3 "$d/checks/itemA_control_check.py"
echo "== A: independent re-scan of the integer minimum =="
run 1 python3 "$d/checks/itemA_scan6.py"
echo "== B: rejection rules R1-R14, 97 objects x 14 rules =="
run 1 python3 "$d/checks/itemB_controls.py"
echo "== C: X4h relaxation, true-window re-run =="
out=$(python3 "$d/checks/itemC_x4h_check.py") || { printf '%s\n' "$out"; exit 1; }
printf '%s\n' "$out" | tail -2 | head -1
echo "== C: clauses of Lemmas 5.2-5.4 on 97 objects =="
run 1 python3 "$d/checks/itemC_lemma_controls.py"
