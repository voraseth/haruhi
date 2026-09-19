#!/bin/sh
# Endpoint-pinned chain queries (paper: Algorithm 4; Proposition 6.6).
# 1. build the exhaustive query engine
# 2. run the counting-route kill battery (profiles -> structure scan ->
#    the nine endpoint-bound eliminations; ~30 s; expect 5544 queries,
#    cells e=5,8,9 DEAD, one surviving configuration each at e=6, e=7
#    and (15,1,0) e=7 -- exactly the three that die in ../covering-test)
# 3. validate the engine against the certified capacity tables
#    (~4 minutes; expect 0 disagreements over 7855 queries)
set -e
cd "$(dirname "$0")"
cc -O2 -o chainq chainq.c
python3 profiles.py
python3 scanhigh.py
python3 killer.py
python3 qvalid.py
