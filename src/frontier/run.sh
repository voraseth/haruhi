#!/bin/sh
# Chain-capacity frontier: the certified tables of Appendix B, their
# pruning-free certification, and the sharpness witnesses.
# (Paper: Lemma 5.10 and Appendix B; reproduction-record rows R1a-R1e.)
#
#   sh run.sh          fast: sharpness check + a de-pruned run to cost 12
#   sh run.sh full     the de-pruned run to cost 16 (2.03e9 nodes, minutes)
#
# The four programs here:
#   chains871.c           the enumerator with dominance pruning (mode B / C / S)
#   chains871_noprune.c   the same file plus ONE line disabling that pruning,
#                         so exhaustiveness is certified rather than assumed
#   chains871_norunkap.c  the same file with TWO lines changed: the residual
#                         structural gate RUNCAP raised 4 -> 100 AND the same
#                         de-pruning line as chains871_noprune.c; bit-identical
#                         output to cost 17
#   chains871_witness.c   the pruned enumerator instrumented to print, for each
#                         non-empty cell, a chain attaining it
#   verify_witness.py     an independent Python re-derivation of rot, rho and d
#                         that checks each printed chain from the definitions
#
# Committed logs are in CERTIFICATES/frontier/:
#   noprune_16.log   nodes = 2,034,132,013     costs 0..16
#   noprune_17.log   nodes = 5,501,025,613     costs 0..17
#   noprune_18.log   nodes = 14,654,518,183    costs 0..18
#   noprune_19.log   nodes = 38,455,866,853    costs 0..19
#   noprune_20.log   nodes = 99,428,989,435    costs 0..20  (128x the pruned run)
#   pruned_20.log    nodes = 778,723,993       the pruned run, same table
#   norunkap_17.log  nodes = 5,501,025,613     RUNCAP gate lifted, identical
#   witness_20.log   the 80 witness chains and the 720-permutation index map
#   witness_verify.log   the independent check: 80/80 attained, 0 failures
#   modeA_runcap.log nodes = 69,840            the LICENCE for RUNCAP = 4
#
# RUNCAP = 4 is the one structural gate that stays in force in every build here,
# including the de-pruned ones, so the certified tables depend on it.  It is not
# assumed: mode A below DERIVES it, by exhausting every chain whose link-paths
# all have length in {4,5} from every one of the 720 head crits, with no cap and
# no pruning, and finding MAXBLOCKS = 4, MAXFOURS = 2, INTERIOR_FOUR = 0 -- the
# statement C6-A.  The same constant licenses chain-query/chainq.c:70,
# covering-test/cover.c:124 and class-scanner/scan871.py:_maxblocks (RC=4,
# RFC=2).  chains871_norunkap.c lifts the gate and reproduces the table to cost
# 17 bit for bit; costs 18..20 rest on mode A.  The run costs 69,840 nodes and
# half a second, and its exit status carries the verdict.
set -e
cd "$(dirname "$0")"
CERT=../../CERTIFICATES/frontier

echo "== C6-A: the licence for the RUNCAP = 4 gate (obligation C12 support) =="
cc -O2 -o chains871 chains871.c
./chains871 A
echo

echo "== sharpness of the frontier (record row R1e) =="
python3 verify_witness.py "$CERT/witness_20.log" | grep -E 'PERM-INDEX-MAP|WITNESS-CHECK|VERDICT'

cc -O2 -o chains871_noprune chains871_noprune.c
if [ "$1" = "full" ]; then C=16; else C=12; fi
echo
echo "== pruning-free enumeration to cost $C (record row R1d) =="
./chains871_noprune B $C
echo
echo "compare the rows above with $CERT/noprune_20.log, which carries the"
echo "same table to cost 20; every row this paper consumes is reproduced there"
echo "by a run with all dominance pruning removed."
