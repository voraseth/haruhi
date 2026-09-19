# Clean-room loop-mode engine (conformance row C11): discharged

The second, independently written loop-mode class-elimination engine.
Row C11 of the conformance ledger (paper, Section 8) is discharged by
what is in this directory.

## Provenance

`src/n6c11_decide.c` was written against the paper's printed
specification alone: Algorithm 6 and Appendix A.6, together with the
model of Section 6.  Its author read no engine source from this
repository or from the working tree it was built in, and did not see
the recorded verdicts of `CERTIFICATES/sweep_all.log` before producing
his own.  The only inputs used were the paper, the length-872 string
printed in it (`data/w872.txt`, extracted from the PDF text), and
`shared/verify6` as a black-box string checker.

The job list was not copied either.  `src/census.py` reimplements
Algorithm G, Algorithm E, Definition F with the coarse capacity table,
and the defect-class expansion of Lemma 5.9, and re-derives the loop
inventory from the paper's printed census:

| class | Alg. G configs | instances | loop runs | paper |
|---|---|---|---|---|
| (20,0,0), e=1..9 | 127 | 320 | 256 | 127 / 320 / 256 |
| (15,1,0), e=1,2,3,4,7 | 69 | 116 | 34 | 69 / 116 / 34 |
| (10,2,0), e=2 | 4 | 5 | 0 | 4 / 5 / 0 |
| (15,0,1) defect (zh/zp3) | n/a | 190 | 190 | n/a / 190 / 190 |
| **total** | **200** | **631** | **480** | 200 / 631 / 480 |

## Result

All 480 loop-mode runs, to complete exhaustion:

    480/480  UNSAT EXHAUSTED     0 accepting records     0 capped

`logs/VERDICTS.txt` holds one line per run.  Every recorded loop run in
`CERTIFICATES/sweep_all.log` is `UNSAT EXHAUSTED`; every run here is
`UNSAT EXHAUSTED`; the instance correspondence is pinned by the exact
census reproduction above.  Agreement is 480/480.

## What the agreement is, and is not

It is agreement of **verdicts**, not of node counts.  This differs from
what an earlier draft of this file predicted, and the reason is worth
stating.  Appendix A.6 as first drafted left four conventions
unfixed (the exit permutation of a run, the defect piece's geometry as
a piece, the endgame branch set, and the meaning of a free anchor), and
two of those change the shape of the search tree.  Two engines that
resolve them differently explore different trees and report different
node counts while returning the same verdicts.  They do:

    campaign engine   1.985e11 nodes over the 480 loop runs
    this engine       198,625,063,259 nodes

So the node count is a fingerprint of one specification, not an
invariant of the theorem.  The verdict is the invariant.  The four
conventions are now stated explicitly in Appendix A.6, as a direct
result of this exercise; an engine written against the current text
should reproduce this engine's counts.

Verdict agreement between two engines would be worth nothing if both
merely rejected everything, so this engine was held to the same three
control classes as the first.  Full record in `logs/CONTROLS.txt`:

- **invariant**: the census totals above, and every structural number
  of the paper's witness remark (145 runs, e=25, P=29 as 25+4, D=25,
  three cost-3 transitions and none heavier, waste=147, type (25,0,0),
  25 type-I cycles, ch=26) re-derived from the raw definitions by
  `src/analyze.py`, with 0 of 141 pointer arcs violating the rho-advance
  that the completeness clause of A.6 relies on;
- **positive**: SAT in linear mode on the real 872's own configuration
  (30 nodes), and SAT in loop mode (6.80e8 nodes, 1 closure) on an
  explicitly constructed loop-carrying placement built by separate
  geometry code (`src/plant4.py`, `data/plant.txt`), so loop mode is
  demonstrably not reject-only;
- **discriminating**: replacing the proved hop rule (a hop has exactly
  six targets) by the content-free "any of the 720" flips instance
  `20-e8#0246` from UNSAT EXHAUSTED in 4,381 nodes to SAT in 1,394
  nodes in linear mode, and in loop mode from 614,946 nodes exhausted
  to over 4e9 nodes without terminating.

## Adjudication of a source-versus-specification deviation

`logs/DEFECT_LINEAR.txt` records a run that is not part of the 480.  A
source audit of the *original* engines found that both inline the next
hop from the zp3 defect piece's exit instead of returning through
`Linear`.  The specification returns through `Linear`, which first
tests whether the instance is complete and, if so, enters the endgame.
So where the defect piece is placed last, the endgame branch at its
exit is a branch of the specified tree the original engines never
evaluate.

This engine does return through `Linear`, so it was run on all 190
defect-class instances in **linear** mode to decide that branch:

    190/190  UNSAT EXHAUSTED     0 accepting records     0 capped
    26,880,043 nodes

The unexplored branch is therefore empty and every verdict stands.  Two
further deviations found by the same audit are vacuous at length 871
(the original heavy pass omits the defect-piece move, and cost-4
closure is restricted to span anchors; both need X4h > 0, which the
defect class does not have).  All three are disclosed in the paper's
verification section.

Reproduce with:

    cc -O2 -o bin_n6c11_decide src/n6c11_decide.c
    awk -F'\t' '$1 ~ /^z1-z/ {print $1" 0 "$3}' data/loopjobs.tsv \
      | xargs -P 7 -I LINE bash -c 'set -- LINE; t=$1; m=$2; shift 2;
          ./bin_n6c11_decide --tag "$t" --mode "$m" "$@" --cap 4000000000000'

## Running it

Everything below runs from inside this directory.  No absolute paths.

Build:

    cc -O2 -o bin_n6c11_decide src/n6c11_decide.c

One cell (the smallest, about a twentieth of a second):

    ./bin_n6c11_decide --tag 20-e9#0252 --mode 1 \
        --n5 16 --n4 0 --n3 2 --n2 0 --n1 0 --c1 8 \
        --spans 2 --bq1 0 --x4h 0 --defect none --cap 4000000000000

Expected, matching the line of the same tag in `logs/VERDICTS.txt`:

    20-e9#0252 mode=1 nodes=65445 closures=9 UNSAT EXHAUSTED time=0.0s

The full sweep (about 1 to 2 hours on 7 cores, ~2e11 nodes):

    ./run_sweep_decide.sh 7

The driver builds the binary if it is absent, reads its 480 jobs from
`data/loopjobs.tsv`, and appends one verdict line per run to
`logs/VERDICTS.txt`.  It is checkpointed: a job whose tag already has a
verdict line is skipped, so the same command resumes an interrupted
sweep.  Move `logs/VERDICTS.txt` aside first if you want a sweep from
scratch.  Any SAT is additionally written to `logs/SAT_ALERT.txt`;
none was produced.

Verdict line format:

    TAG mode=M nodes=N closures=K (UNSAT EXHAUSTED|SAT|CAPPED) time=Ts

`CAPPED` establishes nothing and is never cited; no run reached the cap.

Regenerate the census and the job list from the paper's printed data:

    python3 src/census.py        # writes data/configs.txt, data/instances.txt

Re-derive the witness structure (the invariant control):

    python3 src/analyze.py data/w872.txt

## Files

| path | what |
|---|---|
| `src/n6c11_decide.c` | the engine (Algorithm 6), both modes |
| `src/census.py` | Algorithms G and E, Definition F, defect expansion |
| `src/analyze.py` | structural analyzer for a superpermutation string |
| `src/plant4.py` | constructive loop plant (positive control) |
| `run_sweep_decide.sh` | checkpointed driver for the 480 loop runs |
| `data/instances.txt` | the 631 instances, re-derived |
| `data/loopjobs.tsv` | the 480 loop jobs, tag / mode / arguments |
| `data/plant.txt` | the explicit planted loop placement |
| `data/w872.txt` | the length-872 witness, from the paper |
| `logs/VERDICTS.txt` | one verdict line per run, 480 lines |
| `logs/CONTROLS.txt` | the full control record |
| `logs/DEFECT_LINEAR.txt` | the 190 defect instances in linear mode, adjudicating deviation (i) |
