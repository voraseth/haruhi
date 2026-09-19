#!/bin/sh
# Re-execution of the 1111 class-elimination runs (paper: Section 7, the
# paragraph "Re-execution of the whole elimination"; conformance row C10).
#
# Every one of the 1111 runs has been re-executed by a party other than the one
# that produced it, in two batches, with node counts and closure counts
# identical to the committed log in every case and 0 mismatches:
#
#   batch1/   844 runs (631 linear + 213 loop), from a build of the audited
#             source.  manifest.json carries the argv, expected node count and
#             expected closure count of each.  Log:
#             CERTIFICATES/independent-reexecution.log
#   batch2/   the remaining 267 loop runs plus 34 overlap controls, from two
#             further independent builds (cc -O2 and cc -O3 -march=native).
#             Log: CERTIFICATES/reexecution/batch2-267.log
#
# The job list of batch 2 was not assumed.  genman.py reconstructs all 1111
# jobs from CERTIFICATES/sweep_all.log alone and validates the reconstruction
# by reproducing all 844 argv vectors, modes, node counts and closure counts of
# batch 1; the complement is then the 267.  That is what this script re-runs,
# in about a second.  Re-running the searches themselves takes CPU-weeks.
#
# What re-execution establishes, and what it does not: it shows the executed
# source is deterministic and that its committed log is faithful to what it
# computes.  It does NOT establish that the source computes the model of the
# paper's Section 6; that is conformance row C11, and it is open for loop mode.
# See ../cleanroom-loop/README.md.
set -e
cd "$(dirname "$0")/batch2"
python3 genman.py
echo
echo "expected:"
echo "  parser validation: 844 overlapping jobs, 0 argv/count mismatches"
echo "  total jobs 1111; not re-executed in batch 1: 267"
echo "  by tag : {'20-e1': 58, '20-e2': 45, 'z1-zh': 82, 'z1-zp3': 82}"
echo "committed as CERTIFICATES/reexecution/joblist-reconstruction.log"
