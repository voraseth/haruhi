# STATUS — T-n6-coverage (approaches/n6coverage)

**Mandate.** Close the referee's objection that the bridge "all possible
length-871 candidates --> exactly these 631 computational instances" is not
independently auditable.

**Deliverable.** `coverage.md` (1026 lines) + `checks/` + `logs/`.

## Headline results

| item | status |
|---|---|
| **COVERAGE THEOREM** (sect. 6) | **PROVED — no residual audited-output step** (upgraded 2026-09-03) |
| **Two-loop bound** (Lemma 6.8's "at most two arcs") | **PROVED MATHEMATICALLY** (sect. 5.2) — mandate 4 option (a) achieved; no longer a measurement |
| **Census generator specified as an algorithm** (sect. 3) | DONE — 11 tests, each with a necessity proof (sect. 4) |
| **Over-approximation of the generator** | PROVED (Lemmas 4.1–4.12) |
| **Printed data** (200 configs + 631 instances) | DONE — `logs/census_table.txt`, 910 lines / 53,763 B / 4,958 B gzipped, one-command regeneration |
| **Run-level match to the committed sweep** | EXACT — 1111 runs, 0 missing / 0 extra / 0 SAT / 0 CAPPED |
| **Admission controls** (872, 873, six m2obj at L=877..880) | ALL PASS |
| **Discrimination controls** | ALL PASS (identities alone admit 6513 vs 200; a_2=3 rejected at 871, accepted where real objects have it) |

## The former residual: CLOSED (2026-09-03)

This document originally recorded `a_3 = 0` and `c_2 = 0` — needed because the
engine has no three-block piece and its endgame places only full-orbit cycles —
as *audited outputs* of the census generator rather than hand proofs.  The
sibling agent T-n6-fin (`approaches/n6finlem/finlem.md` sect. 4) produced a
two-tier finite derivation, and I verified it independently
(`checks/tier_check.py`, `logs/tier_check.log`, all PASS):

* **Tier 1** eliminates n45 between my Lemma 4.10 (class budget) and my
  Lemma 4.9 (run caps), giving `N_lo > N_hi` — one integer inequality, no table
  lookup — which kills **140 of the 150** `c_2 >= 1` censuses and **148 of the
  150** `a_3 >= 1` censuses.  I checked algebraically over the whole box that
  `N_lo <= n45 <= N_hi` is *exactly* those two lemmas with n45 eliminated
  (0 mismatches): Tier 1 introduces no new hypothesis.
* **Tier 2** is the Pareto test, which is decided at census level (blocks_rest,
  LAM, cost_rest do not depend on n45 or n4); the remaining **10 + 2** censuses
  each die on one entry of the certified capacity table.  All 11 + 4 printed
  rows DEAD, recomputed with this workdir's own `F`.
* **0 survivors.**  Robust: rerunning with `g(20) = 25` replaced by the weaker
  C6-B bound still gives 0.  Discriminating: the same two tiers admit
  `c_2 >= 1` at (25,0,0) e = 3, 5, 8, 11 and (30,0,0) e = 5, and none at e = 12
  — matching the published e = 3..11 range.
* Every test used is one already proved necessary in coverage.md sect. 4
  (Lemmas 4.9, 4.10, 4.11); the enumerated space is Algorithm G's own box, not
  a narrower one; the value ledger G10 is not used at all.

**My earlier observation that the Pareto ledger is genuinely required now
appears inside the proof rather than as a caveat.**  The ledger-free system
admits `a_3 = 1` at (20,0,0) e = 2 and e = 4 — and those are *precisely* the
two censuses that survive Tier 1 in the `a_3` clause.  They die on four printed
frontier values: 27 > F(2,16,1,1) = 26; 26 > F(1,14,1,0) = 19;
25 > F(2,14,1,1) = 24; 24 > F(1,12,1,0) = 17.

What remains machine-borne is only the computer-assisted core the result is
entitled to: the 1111 exhaustive searches, and the set-equality between the
derived instance list and the committed run log.  Neither is a mathematical
claim quantified over orderings.

## Numbers

* 200 configurations = 127 (20,0,0) + 69 (15,1,0) + 4 (10,2,0); 2 wirings (15,0,1)
* 631 instances = 320 + 116 + 5 + 190
* 1111 runs = 631 linear + 480 loop-complete (exposed = 256 + 34 + 0 + 190)
* printed table: 910 lines, 52.5 KB, 5.0 KB gzipped
* max U = a_2 + 2a_3 over all 200 configurations = 2 (attained); proved <= 2
* c_2 = 0 / a_3 = 0: 300 censuses, 288 killed by one integer inequality, 12 by one certified table value; 0 survivors
* compute used: ~15 CPU-seconds (budget was 30 CPU-min; no search was re-run)

## Required manuscript changes

Five, listed in coverage.md sect. 9.2, with verbatim replacement text for the
two load-bearing ones in sect. 9.4.  Namely: replace Lemma 6.8's census appeal
by the proved two-loop bound; replace Lemma 6.7's "Finite verification" by the
two-tier derivation and print its 11 + 4 Tier-2 rows; print the census
algorithm and the 200/631 table; and stop claiming configuration-layer
independence on the strength of R-n6-7 (whose `myjobs.py` imports the
artifact's `enumerate_cell` and therefore re-derived only the expansion).
