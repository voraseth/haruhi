# Verification: what to run, and what it should print

Three tiers.  Tier 0 takes a minute and checks the theorem's upper half.
Tier 1 takes about twenty minutes and re-runs every argument that is
cheap enough to re-run.  Tier 2 is the elimination itself, which costs
CPU-weeks and is supplied instead as committed run logs plus the
programs that produced them.

Every `src/*/run.sh` is self-contained: POSIX sh, a C compiler and
Python 3, no dependencies, no network, no absolute paths.  Each states
its expected output at the top.  Run them from the repository root or
from their own directory; both work.

## Tier 0: the witness (about one minute)

    sh src/checker/run.sh

Two independently written membership checkers, one Python and one C,
read `data/best872.txt` and print, each:

    length=872 distinct_perms=720 VALID_SUPERPERM6

That establishes `L(6) <= 872`, the upper half of the theorem, from a
certificate a reader can check without trusting anything else here.
The string is printed in full in Section 1 of the paper.

## Tier 1: the arguments that re-run cheaply

| claim (paper) | command | expected | time |
|---|---|---|---|
| Prop. 4.1, upper bound | `sh src/checker/run.sh` | 720/720, twice | seconds |
| Lemma 5.1, Prop. 5.5, Thm. 5.7 | `sh src/class-scanner/run.sh` | 0 classes at 868-870; 18 raw at 871, 16 after the e=0 rows fall to Lemma 5.6; then the elimination table of Section 5, byte-identical to the printed one | ~55 s |
| Lemma 5.10, capacity frontier | `sh src/frontier/run.sh` | 80/80 cells attained, 0 failures, `VERDICT: SHARP`; then a pruning-free table to cost 12 matching `CERTIFICATES/frontier/noprune_20.log` row for row | ~10 s |
| Lemma 5.6, the e=0 slice | `sh src/ordering-search/run.sh` | the four one-node instances, each `solutions=0 ... EXHAUSTED`, matching `CERTIFICATES/e0-exhaustion/` | seconds |
| Lemma 5.8, no cost>=5 transition | `python3 src/finlem/checks/lem58_k1.py` | 0 survivors; ablation; the X4h=2 control leaves 4 | ~10 s |
| Lemma 5.9, the defect-one class | `python3 src/finlem/checks/lem59_z1.py` | 5 branches, 24 wirings, exactly 2 survive | ~2 s |
| Lemma 6.7, cycle-shape exclusion | `python3 src/finlem/checks/lem67_c2.py`, then `cd src/class-elimination && python3 c2_witness.py && python3 differential.py` | 140+10 and 148+2 kills, 0 survivors; mirror survivor sets exact | ~1 min |
| Prop. 6.6, chain kills | `sh src/chain-query/run.sh` | 5544 queries; e=5,8,9 dead; validation 7855 queries, 0 disagreements | ~5 min |
| Prop. 6.6, covering kills | `sh src/covering-test/run.sh` | covers=0 everywhere; control ALIVE | ~5 s |
| Thm. 6.14, coverage | `sh src/coverage/run.sh` | all PASS; 200 configs / 631 instances / 1111 runs; 0 missing, 0 extra | ~8 s |
| Lemma 6.8(3), two-loop bound | `python3 src/coverage/checks/loopbound.py` | max U = 2 under the weakened system | ~2 s |
| Lemma 6.8(1), closure-graph structure | `sh src/closure/run.sh` | 103 objects, 0 violations; `\|V\|` = a2+2a3+1+X4h exact; abstract control 5520/5520 against 960/5520 | ~1 s |
| the printed census table | `python3 src/coverage/checks/print_census.py` | 910 lines; asserts 200 / 631 / 1111 | ~2 s |
| App. C.1, base-bound inequalities | `python3 src/audit/checks/itemA_control_check.py` and `itemA_scan6.py` | 97 objects, 0 violations; min t = 24 | ~10 s |
| App. C.2, rules R1-R14 | `python3 src/audit/checks/itemB_controls.py` | 97 objects x 14 rules, 0 rejections | ~1 s |
| Lemma A.1, X4h relaxation | `python3 src/audit/checks/itemC_x4h_check.py` | survivor cells identical at L=868..873 | ~4 s |
| Lemmas 5.2-5.4 clauses | `python3 src/audit/checks/itemC_lemma_controls.py` | 97 objects, every clause satisfied | ~2 s |
| the 631 linear runs, totalled | `sh src/engine-original/run.sh` | `TOTAL: jobs=631 nodes=10993460947 SAT=0 capped=0`, the 1.099e10 figure of record row R7a | ~5 s |
| the 631 linear runs, **re-executed** | `sh src/engine-original/run.sh replay` | all 631 jobs rebuilt and re-run, every node count diffed against the committed log; `REPLAY PASS`, node total 10993460947 | ~15 min, 9 workers |
| the job list of the 267-run batch | `sh src/reexecution/run.sh` | 844 overlapping jobs, 0 argv or count mismatches; complement 267, split 58 / 45 / 82 / 82 | ~2 s |
| the reproduction record, Table 3 | `cd src/record && python3 gen_record.py` | LaTeX byte-identical to the table between the generated-region markers in `paper/PAPER-n6-872-v2.tex` | instant |
| the external length-872 control | `sh src/external-872-control/run.sh <path>` | 720/720; 0 violations; no rule rejects it; every clause satisfied | ~1 s |
| (R3) the two written scanners | `python3 src/class-scanner/crosscheck_scan6.py` | two distinct md5s; both ladders `0,0,2,8,22,45`; 796 survivor cells identical | ~40 s |
| C6-A, the licence for `RUNCAP = 4` | `cd src/frontier && cc -O2 -o chains871 chains871.c && ./chains871 A` | `MODEA starts=all720 nodes=69840 MAXBLOCKS=4 MAXFOURS=2 INTERIOR_FOUR=0` then `RUNCAP4 PASS`, exit 0 | <1 s |
| the ordering search's positive control | `sh src/ordering-search/run.sh calib873` then `python3 src/ordering-search/verify_e0_873.py out/E0_873_S24_X6.txt` | exactly 96 solutions, EXHAUSTED; each reconstructs to a length-873 superpermutation; the set equals `data/optimal-873/` | ~8 min |
| the query validation at full table depth | `cd src/chain-query && CMAX=18 python3 qvalid.py` | one `ROW` line per row above cost 16, then `249 rows, 993 typed maxima, 10682 queries, 0 failures`; `0 rows unvalidated`; committed as `CERTIFICATES/qvalid-cmax18.log` (63 `ROW` lines whose checks, queries and failures total 252 / 2827 / 0, i.e. exactly the increment over the cost-16 subtotal) | ~63 min |
| the semantic-teeth battery | `sh src/testbattery/run.sh` | verdicts flip where the transcripts say they flip; node counts move where they say they move | ~9 min |

The external control needs a file this repository does not ship; see
`src/external-872-control/run.sh` and `REFERENCES.md`, key `A6872repo`. The
object is third-party material and is deliberately **not** redistributed, so
this row is a genuine gap rather than a pass: an unrun control is not evidence.
What *is* verified here is that the harness around it is live, so that the row
becomes evidence the moment a reader supplies the file. Substituting this
repository's own `data/best872.txt` through the same `SUPERPERM_P872` hook makes
the whole control pass (`checked 97 sequences; 0 violations`, `CONTROL PASS: no
rule rejects any verified object`, `CONTROLS PASS: 97 orderings`, exit 0);
substituting a one-character mutation of it makes the script abort at the
membership stage with exit 1; and the committed transcript
`CERTIFICATES/external-872-control.log` prints the *external* object's own
profile (`L=872 m=143 extra=23 Ncyc=23`), which differs from this project's
witness (`e=25, Ncyc=25, 145 runs`) and so proves the substitution took effect
on the run that produced it.

## Tier 2: the elimination itself

These are supplied as committed run logs.  Re-running them costs
CPU-weeks, and the commands are given so that anyone who wants to spend
that time can.

| computation | command | scale | log |
|---|---|---|---|
| the 1111 class-elimination runs | `cd src/class-elimination && python3 driver.py` | 2.09e11 nodes, ~8 CPU-h per pass of the cheap half and far more for the rest | `CERTIFICATES/sweep_all.log` |
| the nine e=0 ordering searches | `sh src/ordering-search/run.sh all` | 9.0e11 nodes | `CERTIFICATES/e0-exhaustion/` |
| the pruning-free frontier to cost 20 | `cd src/frontier && cc -O2 -o chains871_noprune chains871_noprune.c && ./chains871_noprune B 20` | 9.94e10 nodes, 128x the pruned run | `CERTIFICATES/frontier/noprune_20.log` |
| re-execution, batch 1 (844 runs) | `cd src/reexecution/batch1 && python3 runner.py` | 631 linear + 213 loop | `CERTIFICATES/independent-reexecution.log` |
| re-execution, batch 2 (267 runs + 34 controls) | `cd src/reexecution/batch2 && python3 driver.py` | 1.754e11 nodes | `CERTIFICATES/reexecution/batch2-267.log` |

A search log line counts as evidence only if it ends with an exhaustion
marker.  A `CAPPED` line establishes nothing and is never cited.  All
1111 runs report `UNSAT EXHAUSTED`; 0 SAT, 0 CAPPED, 0 timeouts.

## Re-execution of 2026-09-09

The whole suite was re-run from inside this folder after the final round
of editing, and every item reproduced:

* the coverage census regenerates 200 configurations, 631 instances and
  1111 runs, and every cross-check passes;
* the clean-room frontier sweep is node-identical at 16,571,498,239
  nodes, and identical again with its run gate disabled;
* the defect adjudication is node-identical at 26,880,043 nodes over
  190/190 instances, all UNSAT EXHAUSTED;
* the clean-room loop-mode controls are node-identical;
* every certificate program rebuilds and re-runs;
* a fresh full 480-run loop sweep agrees with the committed verdicts on
  all 480, including node counts;
* `python3 src/record/gen_record.py` regenerates the paper's
  reproduction table byte-identically from `src/record/record.tsv`
  (the two `% BEGIN`/`% END` marker comments in the paper are not
  emitted by the generator and bracket the generated block).

## Re-executing the two full linear-mode campaigns

Both bodies of linear-mode runs can be re-executed from this repository and
compared value by value with their committed logs, not merely re-tallied.

### The 631 runs of `src/engine-original`

    sh src/engine-original/run.sh replay              # about 15 min on 9 workers
    sh src/engine-original/run.sh replay --check-only # validate the job list only

Note that `sh src/engine-original/run.sh` with no argument only *totals* the
eight committed logs; on a copy of this tree with those logs removed it prints
`TOTAL: jobs=0`.  It checks that the shipped evidence is self-consistent.
Re-execution is the `replay` mode.

`src/engine-original/replay_all.py` reads the eight committed logs as its job
list, reconstructs each job's argument vector from the mapping used by the
drivers that produced those logs (`src/class-elimination/mkjobs.py` for the
`realize2` and `realize3` cells, with `nd4` from the section header;
`run_z1real.py` for the `realize4` cells, with the wiring mode from the section
header; and `run_e9.sh` and `run_e78.sh` for the nineteen `realize` jobs whose
two-digit M2 token the logs do not record, matched to the log by its echoed
label).  It rebuilds all four engines from source, runs every job, and compares
the node count of each against the committed one.

It self-checks its job list before running anything: every `N jobs` section
header must equal the jobs parsed for that section, every log's job count must
equal its number of verdict lines, and the total must be 631.  Any line that
does not parse is fatal, so a silently skipped job cannot shrink the job list.

Result, committed as `CERTIFICATES/campaign-original/replay-postfix.log`:
**631/631 `UNSAT EXHAUSTED`, 0 SAT, 0 CAPPED, 0 `INSTFAIL`, and the node count
of every job equal to its committed value**, node total 10,993,460,947, the
1.099e10 of reproduction-record row (R7a).

### The 1111 runs of `src/class-elimination`

    cd src/class-elimination && python3 driver.py        # about 2 h on 9 workers
    python3 cmp_sweep.py <fresh log> ../../CERTIFICATES/sweep_all.log

Result, committed as `CERTIFICATES/sweep-replay-postfix.log`: **1111/1111
`UNSAT EXHAUSTED`, 0 SAT, 0 CAPPED, 0 verdict differences, 0 node-count
differences**, node total 209,483,950,989.  `cmp_sweep.py` keys on each job's
parameter tag rather than on line order, because `driver.py`'s workers finish in
a nondeterministic order and a plain `diff` of the two logs would report
spurious differences.  The fresh run's per-job lines are committed as
`CERTIFICATES/sweep-replay-postfix-runlines.log`, so the comparison is
re-derivable from this repository alone.

### A correction that rides alongside

One committed log carries an incorrect trailing summary line:
`CERTIFICATES/campaign-original/realize_e6.log` ends
`--> e=6: 43 SAT, 0 CAPPED, 0 UNSAT-EXHAUSTED`, although all 43 of its job lines
read `UNSAT ... EXHAUSTED` and the replay returns `UNSAT` for all 43.  Nothing
reads that line: `summary.py` and every figure cited in this file parse the job
lines.  It is left in place, because a committed evidence log is append-only,
and the correction is filed in `CERTIFICATES/campaign-original/ERRATA.md`.

## Driver recording rules

A search program and the driver that records its answer are two different things,
and a clean log proves nothing about the second.  Every driver here now applies
the same rule: **a negative verdict is recorded only when the child's exit status
AND its completion marker both say so.**  Anything else -- a crash, an OOM kill,
a `usage:` line, an empty read, a desynchronised answer -- is reported as
`DRIVER-ERROR` and exits non-zero, never as an elimination.

The exit conventions the rule is written against, each read from its own source
rather than from its driver: `mysweep` and `realize*` return **0 on SAT, 2 on
`UNSAT ... EXHAUSTED`, 3 on a cap** (`mysweep.c`: `return sat ? 0 : 2;`);
`n6c11_decide` returns **1 on SAT, 0 on `UNSAT EXHAUSTED`, 4 on a cap**
(`n6c11_decide.c:485`: `return sat ? 1 : (capped ? 4 : 0);`) -- note that the two
families disagree on which of 0 and 1 means SAT, which is precisely why each
driver encodes its own engine's convention instead of a shared one.  So "the child exited 0" is *not* the test for an
elimination in the first family, and the drivers encode each engine's convention
explicitly.

The three `chainq` drivers (`killer.py`, `qvalid.py`, `bfinal.py`) additionally
parse the six query parameters `chainq` echoes on every answer and compare them
with the parameters sent.  Without that, a single dropped line would shift every
later answer by one, and since a dead or desynchronised `chainq` answers `NO`,
and `NO` is the verdict those programs are looking for, the failure would have
read as a stronger result.  `bfinal.py` also runs a pre-filter control before it
believes any `NO` (`chainq` must find the certified 4-block all-length-5 chain)
and asserts that `cover` was actually invoked.

`src/audit/run.sh` propagates each checker's exit status rather than the exit
status of the `tail` it pipes into.

## The audit battery must not run under `-O`

The structural verification in `src/audit/` is carried by Python `assert`
statements -- 47 in `lib6.py`, 13 in `validate871.py` (counted as AST
`Assert` nodes, not by `grep`, which misses the one-liners:
`python3 -c "import ast,sys;print(sum(1 for n in ast.walk(ast.parse(open(sys.argv[1]).read())) if isinstance(n,ast.Assert)))" FILE`),
and the whole of
`itemA_control_check.profile()`.  Under `python3 -O` or `PYTHONOPTIMIZE=1` every
one of them is removed, and it was measured that all five checkers then printed
their PASS lines with no checking performed.  All five now **refuse to run**
under `-O`:

    PYTHONOPTIMIZE=1 sh src/audit/run.sh      # exits 1, prints the refusal

and the verdict-bearing comparisons (`min t = 24`, the corpus sizes, the clause
failure list) are explicit `if not cond: sys.exit(...)` rather than asserts, so
they survive any interpreter flag.  `itemC_lemma_controls.py` in particular now
reads the failure list `validate871.check()` collects; it previously printed
`CONTROLS PASS` unconditionally, so a real counterexample to Lemmas 5.2-5.4 on a
real object would have been reported as a pass.

## The test battery

`CERTIFICATES/testbattery/` holds a semantic-teeth and boundary battery and its
matrix, `TESTMATRIX.md` (one row per program per test, with the observed
evidence).  It asks the question a clean run log cannot answer: are the proved
constraints the program enforces actually load-bearing, or would the same
verdicts come out with the constraints deleted?

    sh src/testbattery/run.sh

regenerates the four transcripts.  Each variant is a one-line patch applied to a
copy of the source under `$TMPDIR`, and each patch anchor is checked at build
time, so a source change cannot silently turn a teeth test into a no-op.  The
headline results, all reproducible:

* replacing the proved cost-3 hop rule by the content-free "any of the 720"
  flips `mysweep.c` from `UNSAT EXHAUSTED` to `SAT` on two committed instances,
  so the 1111 emptiness verdicts are carried by that rule;
* removing class-disjointness or the hop rule flips `chainq` answers from `NO`
  to `YES`, so its kills are carried by those constraints;
* forcing the rho-4-segment cover test to accept flips every decisive
  configuration of `cover.c` from EMPTY to ALIVE, so the cover test is the
  deciding rule;
* the block bounds of both `chainq` and `cover` are verdict-neutral, as
  soundness requires, and load-bearing computationally (x51 and x27.6 nodes);
* **the `C6-A` run-cap line in `chainq.c` and `cover.c` is inert**: disabling it
  changes not one node.  The `(4-r')` term of the block bound already subsumes
  it.  This is recorded rather than repaired -- an unfiring *restriction* cannot
  cause under-search, and it means those verdicts do not depend on C6-A at all;
* perturbing the class budget `120` of the census generator by one moves the
  configuration count by 65 to 85, so that constant is load-bearing and not on a
  plateau.

## Where each conformance obligation lives

Section 8 of the paper lists twelve obligations, C1 to C12, that an
exhaustive search must discharge before "no solution" means anything.
All twelve are discharged.  This is where the code and the logs
for each row sit.

| row | obligation | program | log |
|---|---|---|---|
| C1 | base-bound inequalities (i)-(vi) | `src/audit/checks/itemA_control_check.py`, `itemA_scan6.py` | `src/audit/logs/itemA_*.log` |
| C2 | rules R1-R14 necessary on every ordering | `src/audit/checks/itemB_controls.py` | `src/audit/logs/itemB_controls.log` |
| C3 | the scanner's four substitutions are weakenings | `src/audit/checks/itemC_x4h_check.py` | `src/audit/logs/itemC_x4h_check.log` |
| C4 | the sixteen classes are exhaustive | `src/class-scanner/scan871.py`, `elimtable.py` | `src/class-scanner/elimtable.txt` |
| C5 | the counting lemmas hold where used | `src/audit/checks/itemC_lemma_controls.py` | `src/audit/logs/itemC_lemma_controls.log` |
| C6 | no transition of cost >= 5 | `src/finlem/checks/lem58_k1.py` | `src/finlem/logs/lem58_full_table.log` |
| C7 | the defect class admits exactly two wirings | `src/finlem/checks/lem59_z1.py` | `src/finlem/logs/lem59_z1.log` |
| C8 | every cycle is type I, no three-block path component | `src/finlem/checks/lem67_c2.py`, `src/class-elimination/c2_witness.py` | `src/finlem/logs/lem67_full_table.log.gz`, `CERTIFICATES/c2_witness.log` |
| C9 | every length-871 superpermutation reaches a committed run | `src/coverage/checks/census_gen.py`, `verify_census.py`, `match_runs.py` | `src/coverage/logs/`, `src/coverage/logs/census_table.txt` |
| C10 | every committed run exhausted | `src/reexecution/` | `CERTIFICATES/sweep_all.log`, `CERTIFICATES/independent-reexecution.log`, `CERTIFICATES/reexecution/` |
| C11 | the engine's source enforces the model and nothing else | `src/class-elimination/mysweep.c` and `src/engine-original/` (linear mode, two written engines); `src/cleanroom-loop/` (loop mode, second engine written from Appendix A.6 alone) | `CERTIFICATES/sweep_all.log`, `CERTIFICATES/campaign-original/`, `src/cleanroom-loop/logs/VERDICTS.txt`, `logs/CONTROLS.txt` |
| C12 | one certified number, the cap 25 at cost 19 (rows 19 and 20 supply it redundantly) | `src/frontier/chains871_noprune.c` and `src/cleanroom-frontier/sweep_decide.c` (two written enumerators) | `CERTIFICATES/frontier/noprune_19.log`, `noprune_20.log`, `src/cleanroom-frontier/logs/run_c20.out`, `run_c20_nogate.out` |

`RUNCAP = 4` is the one structural gate that stays in force in every build of the
capacity enumerator, the de-pruned ones included, so the certified tables depend
on it.  Its licence is now committed: `CERTIFICATES/frontier/modeA_runcap.log`
is mode A of `chains871.c`, which derives the bound by exhausting every chain
whose link-paths all have length in {4,5} from every one of the 720 head crits,
with no cap and no pruning, and finds `MAXBLOCKS=4 MAXFOURS=2 INTERIOR_FOUR=0` in
69,840 nodes.  `src/frontier/run.sh` runs it, and the mode returns non-zero on
failure so its exit code carries the verdict.  Independently,
`src/cleanroom-frontier/c6a_decide.c` re-derives the same bound over all 720
heads, and `chains871_norunkap.c` lifts the gate and reproduces the table to cost
17 bit for bit.

Every row is discharged; the ledger carried open rows through most of
this work.  C12 was the last to close, and its extent was measured by
re-running every consuming stage against the strictly weaker universal
bound.  It is one number: the cap 25 at cost 19, which rows 19 and 20 of
the coarse table supply redundantly, either one sufficing by
monotonicity of g in the cost.  Replacing row 20 alone changes no
emptiness claim, leaves the sixteen classes and the census (200
configurations, 631 instances) untouched, and changes exactly one
published number.  Replacing both rows is not sound: the classification
and Lemma 6.7 survive it, but the census then admits 10 further
configurations expanding to 22 further instances, which were never
expanded and never searched, so the coverage theorem would not land
every candidate in a committed run.  A verdict therefore does rest on
that single value, which is why it was certified a second time rather
than described as verdict-neutral: an independently written enumerator
(`src/cleanroom-frontier/`) reproduced the whole coarse table to cost 20
by complete exhaustion, identically with its run gate disabled, with
C6-A re-confirmed over all 720 heads and the eight attaining chains
re-verified from the definitions.  The exact entries above cost 18 are
supplementary observations; only the bound 25 is consumed.

C11 was the verification boundary of the result until a second loop-mode
engine was written against Appendix A.6 alone, by an author with no
access to either existing engine's source and no sight of the recorded
verdicts.  It re-derived the 480-run loop inventory from the paper's
printed census and returned UNSAT EXHAUSTED on all 480, with no
accepting record and no capped run.  The agreement is at the level of
verdicts, not node counts: the two implementations resolve conventions
that Appendix A.6 did not originally fix, and their node totals differ.
Verdict agreement is evidence because the second engine also passes
positive controls (it returns SAT on a real and on a constructed object)
and a discrimination control (weakening a proved rule flips the verdict
to SAT).  See `src/cleanroom-loop/README.md`.

Six of the sixteen structural classes are in any case emptied twice, by
arguments with no step, no intermediate object and no line of code in
common, one of which uses no search engine at all.

## The reproduction record

Claims about what was reproduced, by how many implementations, and over
what range are made in exactly one place: Table 3 of the paper,
generated from `src/record/record.tsv` by `src/record/gen_record.py`.
Nothing in this file, in the README, or in the paper's prose asserts
more than that table does.  It distinguishes an independently *written*
implementation, which re-derives a computation, from an independent
*build* of one audited source, which re-executes it.

Operational notes. The scripts src/coverage/run.sh, src/closure/run.sh,
src/finlem/run.sh, src/class-scanner/run.sh, src/reexecution/run.sh and
src/testbattery/run.sh regenerate their committed logs in place, and
src/cleanroom-loop/run_sweep_decide.sh appends to logs/VERDICTS.txt.
Regeneration is the check, so a reproduction that succeeds still leaves
those files rewritten and `git status` will show them as modified. That is
expected and is not a sign of a corrupted tree; src/coverage and src/finlem
additionally verify their MANIFEST.sha256 afterwards, so a rewrite that
changed a value would fail loudly. Their outputs are deterministic except
src/class-scanner/elimtable.txt, whose table body is byte-reproducible while
its footer records the elapsed time of the run that produced it. The
byte-identity claims of this file refer to table bodies and value lines,
not to timing footers.

Three programs are cited here but built by no script, because nothing in the
quick suite runs them. Their compile lines are:

    cc -O2 -o src/frontier/chains871_norunkap src/frontier/chains871_norunkap.c
    cc -O2 -o src/frontier/chains871_witness  src/frontier/chains871_witness.c
    cc -O2 -o src/class-elimination/mysweep_c2 src/class-elimination/mysweep_c2.c

All three build with no warnings. `chains871_norunkap` reproduces the capacity
table to cost 17 with the RUNCAP gate lifted; `chains871_witness` emits the
attaining chains; `mysweep_c2` is the type-II branch of the elimination engine,
whose controls are `CERTIFICATES/c2_typeII_controls.log`.

Timing (measured 9 September 2026, one Apple M4, 4 performance + 6
efficiency cores, full re-execution with all stages reproducing the
committed results and the searches node-identical): light checks 184 s;
frontier full sweep 2 m 33 s; defect adjudication 2 s; the 480-run loop
sweep 1 h 02 m (7 workers); the 1111-run class-elimination re-execution
1 h 02 m (6 workers); the nine e=0 ordering searches 2 h 31 m (7
workers, dominated by one irreducibly serial 9,078 s instance).  Back to
back: 4 h 43 m.  With independent lanes overlapped: about 2 h 35 m.
src/ordering-search/run.sh caps runs at 1e12 nodes, overridable via CAP=,
which is above the committed totals of its two largest instances (3.80e11
and 3.97e11).  The script runs its nine jobs sequentially; run them in
parallel for the times above.

The SHORT3 forcing in src/chain-query/scanhigh.py is licensed by clause (5)
of src/chain-query/proofhighe.md, which is shipped verbatim as an evidence
artifact.  That document is a working proof note, and some of its internal
references name documents outside this repository.  The forcing is
load-bearing for that route's own verdict on cell (20,0,0) e=5: with the
clause relaxed, the cell moves from dead to alive.  The route is redundant
with the exhaustive searches, which cover the same cell independently and
do not consult this code.
