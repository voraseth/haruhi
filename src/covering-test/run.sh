#!/bin/sh
# Covering obstruction (paper: Algorithm 5; Proposition 6.6).
# Builds cover.c (and the chainq helper it drives), then runs the
# complete exact-split sweep of the three surviving configurations plus
# the positive control.  Expected: every enumeration EMPTY (covers=0)
# and the length-872 control ALIVE (covers=1).  ~3 minutes.
set -e
cd "$(dirname "$0")"
cc -O2 -o cover cover.c
cc -O2 -o chainq ../chain-query/chainq.c
python3 bfinal.py
