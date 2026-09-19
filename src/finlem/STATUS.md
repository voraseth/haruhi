# T-n6-fin STATUS — referee objection on Lemmas 5.8 / 5.9 / 6.7: ADDRESSED

VERDICT: all three lemmas now have COMPLETE derivations.  None is downgraded;
no rejection test was found that I could not prove necessary.  The theorem
L(6) >= 872 is unaffected in substance; four prose corrections are recommended.

| lemma | status | how it is now established |
|---|---|---|
| 5.8 no cost->=5 transition | COMPLETE | hand reduction to one cell; 5-census table (3 die on a deficiency count); a closed-form N_lo/N_hi pinch leaves ONE candidate, which fails F(2,8,0,0)=20 by margin 4 |
| 5.9 defect-one class (15,0,1) | COMPLETE | 5-branch table (3 die on one F value); wiring lists GENERATED MECHANICALLY from the nc-run edge census (3 shapes per branch, matching R-n6-6's hand list); 26 wirings+refinements decided, exactly 2 survive |
| 6.7 no type-II cycle | COMPLETE | closed-form inequality N_lo > N_hi kills 140/150 censuses in one line each; the other 10 die on one certified frontier value each; companion clause a3=0 by the same two tiers (148+2) |

CASE-TABLE SIZES (appendix-suitable subset ~45 rows; full logs kept):
  5.8  census 5 rows, closed-form 4 rows, deciding candidate 1 row;
       full per-candidate table 4804 rows (logs/lem58_full_table.log)
  5.9  branch 5 rows, wiring+refinement 26 rows (logs/lem59_z1.log)
  6.7  Tier 1 150 rows, Tier 2 11 rows, a3-clause 150 rows, per-class 16 rows;
       full per-candidate table 54233 rows (logs/lem67_full_table.log)

CONTROLS (all asserted inside the scripts):
  * verified 872, (25,0,0) e=25 S=4 X4=0: 1 configuration survives and it IS
    the real 872's shape (a1=4 length-5 paths, c1=25 type-I cycles).
  * verified 873s, (0,6,0) e=0 X4=6 (X4h=5): survives at its real X4h.
  * (10,2,0) e=2 X4h=2 (sibling of the 5.8 cell): 4 configurations survive
    (registered count) -- the kill is specific to X4h=1.
  * DISCRIMINATION for 6.7: the same constraint system ADMITS c2>=1 at
    (25,0,0) e=3..11 (exactly the published range) and at 30 (D,e) cells with
    D in {25,30}.  Engine-level: n6c2probe's type-II-capable sweep regresses
    node-for-node and finds a planted type-II census SAT.
  * ROBUSTNESS: dropping the one un-re-derived table value g(20)=25 (cap-mode
    'lin', C6-B only beyond cost 16) changes no verdict and keeps all controls.
  * FIDELITY: checks/diffcheck.py -- survivor-set equality with
    n6tight/checks/tight_enum.py on 16 habitat + 6 control cells: PASS.

NEW EVIDENCE PRODUCED HERE (beyond restating the record):
  * a FOURTH independent enumeration of the chain Pareto frontier to cost 16
    (checks/chainpareto.c recompiled: 740,052,451 and 2,034,132,013 nodes);
  * the closed-form N_lo/N_hi kill, which turns Lemma 6.7 from a 54k-candidate
    machine sweep into 150 one-line arithmetic checks plus 11 frontier lookups;
  * a MECHANICAL wiring generator for Lemma 5.9 (completeness no longer rests
    on a hand-written case list);
  * six new refinement wirings for 5.9 (zh-emitter / global-end designations)
    never tested by z1_corner.py -- all DEAD, which is what actually pins the
    two surviving skeletons;
  * a proof of REFINEMENT MONOTONICITY (finlem.md sect. 3.4) showing that the
    generic wiring suffices, so the refinement list is provably exhaustive.

PROSE CORRECTIONS RECOMMENDED FOR THE PAPER (no theorem changes):
  1. 5.8: the run cap and the value ledger are REDUNDANT (ablation 0/0/0/1);
     the class budget + frontier kill the cell alone.  F(2,8,0,0)=20, not 21.
     (This is R-n6-6 finding F1/F2, still unrepaired in proof_tight.md sect.7.)
  2. 5.9: cite the mechanical wiring enumeration, not a hand list.
  3. 6.7: state the Tier-1 closed form; record the a3=0 clause's proof.
  4. replace "reproduced independently" by the specific evidence.

COMPUTE: ~40 s total (frontier re-enumeration 32 s, all Python < 8 s).

FILES: finlem.md (the three treatments), NOTES.md,
  checks/{frontier,census,diffcheck,lem58_k1,lem59_z1,lem67_c2}.py,
  checks/chainpareto.c, logs/*.
