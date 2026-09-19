#!/bin/sh
# Regenerate every closure-graph log.  Run from anywhere.  ~10 seconds.
set -e
cd "$(dirname "$0")/../.."          # repository root
python3 src/closure/checks/cgcheck.py \
    data/best872.txt \
    data/counterexamples/m2obj_*.txt \
    data/optimal-873/*.txt > src/closure/logs/cgreal.log
echo "OK  src/closure/logs/cgreal.log   (103 objects)"
python3 src/closure/checks/cgabstract.py > src/closure/logs/cgabstract.log
echo "OK  src/closure/logs/cgabstract.log"
python3 src/closure/checks/symbolic.py  > src/closure/logs/symbolic.log
echo "OK  src/closure/logs/symbolic.log"
