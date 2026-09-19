#!/bin/sh
# The external length-872 control (paper, Section 7, "Audit controls").
#
# A second length-872 superpermutation, produced by an unrelated project and by
# an unrelated method, was published in July 2026 as
#   github.com/vlad-ds/a6-872 , file witnesses/872_nonsaturated_counterexample.txt
# (see REFERENCES.md, key A6872repo).  It is a control this project could not
# manufacture for itself: an object outside its own corpus, on which the
# constraint system built here can be tested for over-tuning.
#
# That string is third-party material and is NOT redistributed in this
# repository.  Retrieve it yourself and pass its path:
#
#     sh run.sh /path/to/872_nonsaturated_counterexample.txt
#
# The script then (1) re-verifies it with both membership checkers and
# (2) substitutes it for this project's own witness in the 872 slot of the
# 97-object control corpus and re-runs all three audit batteries.
#
# Expected output, and the outcome recorded in the paper:
#     length=872 distinct_perms=720 VALID_SUPERPERM6      (twice)
#     profile  L=872  m=143 runs  extra(e)=23  Ncyc=23  Delta=2
#     checked 97 sequences; 0 violations                   (inequalities i-vi)
#     CONTROL PASS: no rule rejects any verified object     (rules R1-R14)
#     CONTROLS PASS: 97 orderings, every clause ... satisfied (Lemmas 5.2-5.4)
#
# The profile differs from this project's witness (e=25, Ncyc=25, 145 runs), so
# the two are not relabellings or rotations of one another: this is a second and
# structurally different point of the constraint system, not a restatement of
# the first.
#
# A committed transcript of this run is CERTIFICATES/external-872-control.log.
set -e
W=$1
if [ -z "$W" ]; then
  echo "usage: sh run.sh /path/to/872_nonsaturated_counterexample.txt" >&2
  echo "(retrieve it from github.com/vlad-ds/a6-872, witnesses/)" >&2
  exit 2
fi
cd "$(dirname "$0")/../.."
W=$(cd "$(dirname "$W")" && pwd)/$(basename "$W")

echo "== membership check (Algorithm 1) =="
python3 src/checker/checker.py "$W"
cc -O2 -o src/checker/verify6 src/checker/verify6.c
./src/checker/verify6 "$W"

export SUPERPERM_P872="$W"
echo
echo "== base-bound inequalities (i)-(vi), 97 objects =="
python3 src/audit/checks/itemA_control_check.py | sed -n '1p;$p'
echo "== rejection rules R1-R14, 97 objects x 14 rules =="
python3 src/audit/checks/itemB_controls.py | tail -1
echo "== clauses of Lemmas 5.2-5.4, 97 objects =="
python3 src/audit/checks/itemC_lemma_controls.py | tail -1
