# Item C audit — T-n6-auditC (resumed after 529 drops)
Date: 2026-08-24. Deadline-driven; one item per turn.

## Work items
1. C2 — X4h relaxation: DONE — CONSERVATIVE RELAXATION PROVED (Lemma C2.1 in itemC_proofs.md; checker checks/itemC_x4h_check.py PASS, log logs/itemC_x4h_check.log; direction table: all X4h occurrences on RHS of <=-caps with +1 coeff, downstream uses dead or fully enumerated)
2. Lemma 5.3: DONE — (b) FINITE-CHECK with sufficiency PROVED (gS exhaustive to cost 18, 8.3e9 nodes; habitat chains cost <=20 with proved fallback caps for 19-20; WLOG-relabelling argument audited; exact bookkeeping identities proved). See itemC_proofs.md.
3. Lemma 5.4: DONE — (a) PROVED (proof871.md section 5 clauses (i)-(v) audited step-by-step from registered L2, 2(c), L12-n6, pool taxonomy; GROUPTYPES completeness m_g<=3 proved). See itemC_proofs.md.
4. Lemma 5.2: DONE — (a) PROVED (proof871.md section 3 from E3-n6 + LEMMAC-n6, registered; frontier envelope use is a sound relaxation; shares the certified C6-C table dependency with 5.3). See itemC_proofs.md.

Priority order per coordinator: C2 first, then 5.3, 5.4, 5.2.
Controls: verified 872 (e=25, S=4, X4=0); 96 verified 873s (e=0, S=24, X4=6).

## Controls
97/97 real orderings (verified 872 + all 96 verified 873s) pass every clause of 5.2/5.3/5.4 (checks/itemC_lemma_controls.py, logs/itemC_lemma_controls.log). X4h checker: survivor cells identical under as-run and true-X4h semantics for L=868..873; both control cells alive under both semantics.

## Bottom line
No undischarged (c). C2 conservative relaxation PROVED (paper needs a wording fix, not a retraction). 5.4 and 5.2 PROVED; 5.3 FINITE-CHECK with the previously missing sufficiency argument now supplied and audited. Total audit compute ~4 s.
