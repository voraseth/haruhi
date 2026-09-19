#!/bin/sh
# Loop-complete class-elimination engine (paper: Algorithm 6;
# Proposition 6.8).  This script builds the engine and runs two quick
# demonstrations:
#   (a) the positive control: the structural census of the real
#       length-872 superpermutation is found SAT (the engine accepts a
#       realizable configuration);
#   (b) the complete battery for class (20,0,0) e=9 -- all searches
#       UNSAT EXHAUSTED, node counts matching CERTIFICATES/sweep_all.log.
# The FULL 1111-run sweep of all sixteen classes is:
#       python3 driver.py            # ~8 CPU-hours, 2.09e11 nodes
# and its committed output is CERTIFICATES/sweep_all.log.
set -e
cd "$(dirname "$0")"
cc -O2 -o mysweep mysweep.c
echo "== positive control: length-872 census (expect SAT) =="
./mysweep 4 0 0 0 0 25 0 0 0 0 0 0
echo "== class (20,0,0) e=9: complete battery "
echo "   (8 instances x 2 modes m0/m1 = 16 runs, all UNSAT EXHAUSTED) =="
python3 driver.py 20-e9
