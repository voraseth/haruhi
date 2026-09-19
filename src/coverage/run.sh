#!/bin/sh
# Regenerate every coverage log.  Run from the repository root.  ~8 seconds.
set -e
# Resolve this script's directory absolutely before any cd, so that the
# manifest paths below are cwd-independent: "$0" is relative when the script
# is invoked from its own directory, and a second `dirname "$0"` after the cd
# would then resolve to the wrong place.
HERE=$(cd "$(dirname "$0")" && pwd)
cd "$HERE/../.."                    # repository root
for f in verify_census loopbound controls match_runs tier_check; do
  python3 src/coverage/checks/$f.py > src/coverage/logs/$f.log
  echo "OK  src/coverage/logs/$f.log"
done
python3 src/coverage/checks/print_census.py > src/coverage/logs/census_table.txt
echo "OK  src/coverage/logs/census_table.txt   (200 configurations, 631 instances)"

# The integrity manifest covers these checks and logs.  It is verified here,
# where the files it covers have just been regenerated, and the script fails
# loudly and names the file if any digest no longer matches.  A manifest that
# nothing verifies goes stale silently.
( cd "$HERE" && shasum -a 256 -c MANIFEST.sha256 >/dev/null ) \
  && echo "OK  src/coverage/MANIFEST.sha256   (all digests match)" \
  || { echo "FAIL src/coverage/MANIFEST.sha256 is stale:" >&2
       ( cd "$HERE" && shasum -a 256 -c MANIFEST.sha256 2>&1 | grep -v ': OK$' ) >&2
       echo 'regenerate with: cd src/coverage && shasum -a 256 $(cut -c67- MANIFEST.sha256 | sed "s/^ *//") > MANIFEST.sha256' >&2
       exit 1; }
