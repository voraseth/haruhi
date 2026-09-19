# NOTES — T-n6-coverage

## What I found that was not already known

1. **R-n6-7's closure-topology theorem does NOT prove the two-loop bound.**
   Its §2.4 proves the shape (path + disjoint loops; only d4 junctions
   temporally immediate; every loop needs an M2/B arc) but ends with
   "#(M2 pieces) + #(B pieces) <= 2", asserted from the census — the same
   measurement the referee objected to in the manuscript.  The referee had NOT
   simply missed a proof.  coverage.md sect. 5.2 supplies it.

2. **The two-loop bound has a two-line arithmetic core.**  From
   D = sum over link-paths of (5 − l) and the TC2 component caps,
   `5(a_2 + 2a_3 + c_2) <= D − e − Delta_1`.  At L = 871 the corners have
   D = 20/15/10, which forces <= 2 everywhere except (20,0,0) at e in {3,4,5},
   and those six residual cases die on the C6-A run caps.  It uses neither
   ledger and neither the census output nor any search log.

3. **The bound is length-driven, and that is checkable on real objects.**  The
   same inequality permits U = 3, 4, 5 at L = 877, 878, 880 — and the six
   R-n6-7 counterexample objects realise exactly those values, four of them
   *at the bound*.  This is the strongest available control on the bound: it is
   tight on real objects and it is not vacuous.

4. **The value ledger (G10) is verdict-neutral at L = 871** — ablating it
   revives 0 of the 200 configurations.  Independently reproduces the
   artifact's own `probe_kill.py` finding.  Good news: one fewer load-bearing
   test.

5. **The configuration layer had never been independently re-implemented.**
   R-n6-7's `myjobs.py` and `driver.py` both `from tight_enum import
   enumerate_cell`; they re-derived the *expansion* only.  `checks/census_gen.py`
   is the first second implementation of the configuration layer, and it
   enumerates a different space (full length multiset vs collapsed tuple +
   interval window).  Result: exact agreement, 200 = 200, class by class.

6. **The TC2c ablation reproduces a published number.**  Turning the cycle
   closure equality off gives 274 configurations, which is exactly the
   artifact's published pre-TC2c census (194 + 76 + 4).  A regression on a
   number nobody had re-derived.

## Design decisions

* I did not re-run any of the 1111 searches (~7 CPU-hours, budget was 30
  CPU-min).  The bridge the referee attacked is the *specification* side, not
  the verdict side; the verdicts already have two independent engines and
  node-for-node agreement.  What was missing and is now supplied is the proof
  that the specification covers everything.
* `checks/pareto.py` reproduces every F-value quoted in proof_tight.md §7 as a
  regression; the GTAB numbers themselves are the certified table (data), so
  they are shared by construction — that is what a certified table is for.
* The ablation harness lives inside `census_gen.gen_cell(..., off=(...))` so
  ablations run the *same* code path as the real census, not a patched copy.

7. **(2026-09-03) The a_3 = 0 loose end closed, and my diagnosis of it was
   right on the nose.**  I had written that the ledger-free system admits
   a_3 = 1 at (20,0,0) e = 2 and e = 4 and that only the Pareto ledger kills
   them.  T-n6-fin's two-tier derivation shows those are *exactly* the two
   censuses (of 150) that survive the closed-form Tier-1 pinch in the a_3
   clause — so the caveat and the proof are the same fact seen from two sides.
   Four printed frontier values finish them.  Verified independently in
   `checks/tier_check.py` with this workdir's own F.
   What made it work was not a new lemma but an *algebraic elimination*:
   removing n45 between the class budget and the run cap turns a 54k-candidate
   sweep into 300 one-line checks.  Worth remembering as a technique — several
   other "finite verification" steps in this project may collapse the same way.

## Loose ends a follow-up could close
* No hash manifest pins the C engines in `n6tight/checks` or
  `R-n6-7-workdir/mysweep`; sources only.  Unchanged from R-n6-7's
  recommendation; not this document's scope.
