# T-n6-fin working notes

## What the objection actually was, and what fixes it

The referee's complaint was not that the lemmas are false but that the PDF
gives a reader nothing to check: "finite feasibility eliminations ...
reproduced independently", with no enumeration, no case table, no algorithm.
Three things were missing and are now supplied:

1. an ALGORITHM SPECIFICATION (finlem.md sect. 1.1) -- inputs, enumeration
   ranges, the seven rejection tests with their formulas;
2. a COMPLETENESS PROOF (sect. 1.1 ranges, sect. 1.3 tests) showing the
   enumerated space is a superset of what real 871s induce -- this is the
   crux, because an unproved rejection test would invalidate the elimination;
3. PRINTED CASE TABLES at a size a paper can carry.

## The three derivations, in one paragraph each

* 5.8 reduces by pure arithmetic (X4h <= X4 <= 3*X4h) to the single cell
  (10,2,0) e=2 X4h=1.  There the five TC2 censuses each have an EXACT
  deficiency floor (a3-component 12, a2-component >= 6, type-I cycle 1,
  type-II cycle 7); two exceed D=10 immediately.  The class-length budget and
  the run cap then pinch n45 from both sides; only census (0,0,2,0) survives
  the pinch, at n45=20 exactly, forcing n4=0.  That one candidate needs 24
  paths in 2 chains of total cost 8 and F(2,8,0,0)=g(4)+g(4)=20.

* 5.9 is a Z=1 corner, so TC2/TC3/TC4 are NOT available as stated (they assume
  Z=0).  The derivation therefore works from the raw event census: which
  transitions land on non-critical permutations (they are the nc-run in-edges)
  and how the premature run ends exit (they are the nc-run out-edges).  That
  census is forced by the pool holding the Z unit, and it determines the
  component shapes mechanically.  Three pools die on P=27 > F(2,15,.,.); the
  other two give 3 shapes each, 26 wirings with refinements, 2 survivors.

* 6.7 is Algorithm A with c2 >= 1 forced.  The presentational discovery is
  that the two tests that survive the census level -- the class budget's lower
  bound on n45 and the run cap's upper bound -- can be combined BEFORE
  enumerating (n45,n4), giving one inequality per census.  140 of 150 die
  there; the remaining 10 die on a frontier value that is also census-level.

## Things worth flagging to the next agent

* R-n6-6 findings F1 and F2 are STILL UNREPAIRED in
  approaches/n6tight/proof_tight.md sect. 7 (the false ablation sentence and
  "F(2,8,0,0)=21").  PAPER-n6-872.tex does not repeat them, but the artifact
  does; anyone reading proof_tight.md will hit them.
* z1_corner.py tests 13 wirings; the complete list including the zh-emitter
  and global-end designations is 26.  All the extra ones die, so nothing
  changes, but the paper's claim "each with its complete skeleton determined"
  was only justified after they were run.  It is now.
* The one table value nobody in this project has re-enumerated from scratch is
  g(20)=25 (used only via cap(c,a,b) for 17 <= c <= 20).  finlem.md sect. 4.5
  shows no verdict here depends on it.  Someone should still re-derive it, or
  the paper should state the C6-B fallback is what is used.
* The rejection tallies published in the paper ("258 candidates, 229/23/6")
  count an n45-slice as ONE candidate when the run cap kills the whole slice.
  The full-tuple count for the same cell is 378.  Both are printed here
  (census.tally vs census.tally_slice); the paper should say which it means.
* Algorithm A's tests are order-sensitive only in the WITNESS, never in the
  verdict: the survivor set is the intersection of all seven tests.

## Verification map

| claim | script | log | marker |
|---|---|---|---|
| frontier rows 0..16 re-enumerated | chainpareto.c (CMAX=15,16) | frontier_c15/16.log | nodes=740052451 / 2034132013 |
| F values used by 5.9 | frontier.py | (stdout) | F SELF-CHECK: PASS |
| census mirrors tight_enum | diffcheck.py | diffcheck.log | DIFFERENTIAL: PASS |
| 5.8 cell empty, controls, ablation | lem58_k1.py | lem58_k1.log | LEMMA 5.8 VERDICT |
| 5.8 per-candidate witnesses | lem58_k1.py | lem58_full_table.log | 4804 rows |
| 5.9 branches + wirings | lem59_z1.py | lem59_z1.log | LEMMA 5.9 VERDICT |
| 6.7 two tiers, a3 clause, controls, discrimination | lem67_c2.py | lem67_c2.log | LEMMA 6.7 VERDICT |
| 6.7 per-candidate witnesses | lem67_c2.py | lem67_full_table.log | 54233 rows |
