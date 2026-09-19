#!/bin/sh
# Structural-class enumeration (paper: Algorithm 2; Lemma 5.1,
# Proposition 5.5, Theorem 5.7).  With the full constraint set (SCG)
# expected output: corners=0 (no surviving classes) at L=868, 869, 870,
# and 4 types / 18 raw classes at L=871; removing the e=0 rows, which
# the separate exhaustion of Lemma 5.6 (CERTIFICATES/e0-exhaustion/)
# eliminates, leaves the paper's 16 classes.  Runs in ~20 seconds.
set -e
cd "$(dirname "$0")"
python3 scan871.py SCG

# Elimination record (paper: Table "Elimination record", Section 5).
# Regenerates the per-type deciding-rule table printed in the paper,
# driving scan871.py unmodified.  Writes elimtable.{txt,tex,csv}.
# Runs in ~35 seconds.
python3 elimtable.py
