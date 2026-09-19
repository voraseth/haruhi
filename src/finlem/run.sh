#!/bin/sh
# Regenerate the Lemma 5.8 / 5.9 / 6.7 derivation logs.  Run from anywhere.
# The three python checks take about a minute in total.  The capacity-table
# re-certification (chainpareto.c) is optional and takes ~30 s to cost 16.
set -e
# Capture this script's own directory absolutely, before any cd: "$0" is
# relative when the script is invoked from its own directory, so a second
# `dirname "$0"` after the cd below would resolve to the wrong place.
HERE=$(cd "$(dirname "$0")" && pwd)
cd "$HERE/../.."                    # repository root
python3 src/finlem/checks/frontier.py   > src/finlem/logs/frontier_selfcheck.log
python3 src/finlem/checks/diffcheck.py  > src/finlem/logs/diffcheck.log
python3 src/finlem/checks/lem58_k1.py   > src/finlem/logs/lem58_k1.log
python3 src/finlem/checks/lem59_z1.py   > src/finlem/logs/lem59_z1.log
python3 src/finlem/checks/lem67_c2.py   > src/finlem/logs/lem67_c2.log
echo "OK  src/finlem/logs/"
# optional: re-certify the chain capacity frontier from scratch
#   cc -O2 -o /tmp/cp16 src/finlem/checks/chainpareto.c && /tmp/cp16 16

# Verify the integrity manifest rather than shipping it unchecked.
( cd "$HERE" && shasum -a 256 -c MANIFEST.sha256 >/dev/null ) \
  && echo "OK  src/finlem/MANIFEST.sha256   (all digests match)" \
  || { echo "FAIL src/finlem/MANIFEST.sha256 is stale:" >&2
       ( cd "$HERE" && shasum -a 256 -c MANIFEST.sha256 2>&1 | grep -v ': OK$' ) >&2
       exit 1; }
