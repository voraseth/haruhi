#!/bin/sh
# Verifies the length-872 superpermutation (paper: Proposition 4.1).
# Expected: length=872 distinct_perms=720 VALID_SUPERPERM6  (twice)
set -e
cd "$(dirname "$0")"
python3 checker.py ../../data/best872.txt
cc -O2 -o verify6 verify6.c
./verify6 ../../data/best872.txt
