# STATUS — approaches/n6cg

**Task.** Repair `report/PAPER-n6-872.tex` Lemma 6.8 (Closure topology), whose
stated vertex set ("chains that are not forced singletons") is inconsistent
with the count used in its own proof (they differ by a_3 + b_q1).

**Result: THE REPAIR HOLDS.  Lemma 6.8 is TRUE as re-proved; nothing downstream
breaks; the two-loop bound is untouched; the theorem is NOT open at this point.**

| item | status |
|---|---|
| Intended object established from code + source artifacts | DONE — `V(CG)` = hop-chains **not lying in pointer cycles** ("free chains"); verbatim in `n6coverage/coverage.md` §5.1 and `reviews/R-n6-9.md` §1(a); implemented by `mysweep.c` (l.196/288/348) |
| Lemma 6.8 re-proved in full from raw definitions | DONE — `cg.md` §2 |
| Do the newly-included chains (a_3 middles, q_1's path) break any step? | NO — both have exactly the degrees the argument needs; q_1's chain is *required*, being the claimed source. The **printed** definition is the one that breaks part (1) |
| Two-loop bound re-verified | INDEPENDENT of the vertex set — it bounds the *arc* count U = a_2+2a_3 by deficiency accounting; `coverage.md` §5.2 stands verbatim |
| Downstream audit (8 citation sites + coverage.md §6.2(e)) | DONE — all survive verbatim; none needs the printed set |
| Controls on real objects | 103 objects (872, 96×873, 6 counterexamples), **0 violations**; \|V\| = a_2+2a_3+1+X4h exact in every one; k = 0,0,1,3,4,4,4,5 |
| Discrimination control (a_3>0 / b_q1=1, absent from all real objects) | DONE — abstract TC1-end/TC3 model, 5520 trials: corrected 5520/5520, as-printed 960/5520 (passes exactly where the definitions coincide) |
| Drop-in LaTeX (statement + proof part (1) + correction remark) | DONE — `cg.md` §6 |

**Honest negative.** No object in the repo has a_3 > 0 or b_q1 = 1, so the real-
object controls confirm the corrected count but cannot by themselves refute the
printed one; that discrimination rests on the abstract control (`cg.md` §5.2)
and on the proof.

Deliverable: `cg.md`.  Scripts in `checks/`, outputs in `logs/`.
