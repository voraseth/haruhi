# Item A audit — Lemma 3.4's six inequalities (i)-(vi)  [COMPLETE]

Auditor: T-n6-audit (scope restricted to Item A by coordinator).
Full written proofs: itemA_proofs.md (journal-standard, self-contained,
dependency-ordered, n=6). Checkers: checks/itemA_control_check.py,
checks/itemA_scan6.py; logs in logs/.

Claim audited: the class-occupancy system over
(x=extra, x3=e3, d2, f=F, q=Q2, c=Ncyc, a=alpha, y=h=X4, m=120+x,
Delta, PT) whose integer minimum t = x+a+y = 24 gives W >= 143, i.e.
L(6) >= 868 (paper Lemma 3.4 / "Base bound").

TRUE SOURCE: approaches/bounds/bounds.md (the "companion formalism" the
paper cites), sections 3, 6, 7, 8. The paper's one-paragraph proof is a
faithful summary; every inequality has a genuine written derivation there.

## Classification table

| Ineq | Statement | Verdict | Source (bounds.md) | Proof here | Depends on |
|---|---|---|---|---|---|
| (i)   | q + c <= x                    | (a) PROVED | Lemma 12 (§6), via Lemmas 10, 11 | itemA_proofs.md §2 | A3, A4 <- A1, P1-P6 |
| (ii)  | q <= x3                       | (a) PROVED | Lemma 16 (§8), via Lemma 10(2,4) | itemA_proofs.md §2 | A3 <- P2, P5 |
| (iii) | Delta >= 0                    | (a) PROVED | (C6) (§6), from Lemma 9 | itemA_proofs.md §1 | A1 <- P1-P3 |
| (iv)  | PT >= 1+a+q-Delta-(f-c)       | (a) PROVED | Lemma 17 (§8) | itemA_proofs.md §3 | A1, A2, A4 |
| (v)   | PT <= floor(m/5)              | (a) PROVED | asserted in Thm-5 list (§8); one-line proof supplied | itemA_proofs.md §3 | def. of PT |
| (vi)  | 5 PT <= 4(2+y+a+f)            | (a) PROVED | Lemmas 18, 19(3) (§8) + #segments <= 1+a+f | itemA_proofs.md §4 | A5-A8 <- P3, A3, A7 |
| min t = 24 | integer minimum of (i)-(vi) | (b) FINITE-CHECK, range-sufficiency PROVED | checks/certify_scan.py; Thm 5 (§8) | itemA_proofs.md §5 (Prop A11) | (i)-(vi), A9, A10 |

Auxiliary lemmas also audited (used by the scan):
- dirty <= d2 + floor(x3/2): (a) PROVED (Lemma A9, trivial counting; stated inline in paper and bounds.md §8).
- monotone relaxation in f (scan at maximal dirty is conservative): (a) PROVED (Lemma A10; direction check: f enters (iv) negatively on a lower bound, (vi) positively on an upper bound — both relaxing).

## Range sufficiency for the finite check (why (b), not (c))

t = x + a + y with all three summands >= 0, so any ordering with t <= 23
has x, a, y <= 23; all remaining variables are bounded by x (x3 <= x,
q <= x3, c <= x - q, m = 120 + x, PT <= floor(m/5)). The scan over
t <= 28 therefore covers every ordering that could beat 24; its
infeasibility below 24 is conclusive. Proof written out as Prop. A11.

## Verification evidence (computer-assisted standard)

- Independent reimplementation, this audit: checks/itemA_scan6.py
  (written from the constraint list alone) -> min t = 24 at
  (0,0,0,0,24,0), Delta=5, PT=20 — matches the paper's stated tight
  profile and bounds/logs/certify_scan10.log, certify_scan11.log.
- Discrimination controls: checks/itemA_control_check.py recomputes all
  profile variables from raw definitions on the verified 872 and all 96
  verified 873s; asserts the structural lemmas (component sizes, rho
  advance, chain count, cost identity) AND (i)-(vi): 97/97 pass, 0
  violations (logs/itemA_control_check.log). Controls are non-trivial:
  872 is TIGHT in (i) (q+c = 25 = x) and (iii) (Delta = 0); the 873s
  are TIGHT in (v) (PT = 24 = m/5) and (iii).
- Source-side evidence: bounds/checks/stretch_check.py (4200 random +
  semi-greedy sequences n=4,5,6 + all 345 near-opt n=4), pointer_check.py
  (345 n=4 sequences, 206 pointer cycles), random_adversarial.py (6300
  sequences) — zero violations of Lemmas 9-19 per bounds.md §6, §8;
  calibration: same system gives the exact L(5) = 153.

## Circularity check

Dependency DAG written out in itemA_proofs.md §7: roots are elementary
computations (P1-P3) + Hamiltonicity; every lemma cites only earlier
ones; none of (i)-(vi) assumes any length/cost/type restriction, so the
system is valid for EVERY ordering (as required for use as search cuts).
ACYCLIC — no circularity found.

## Verdict on Item A

All six inequalities: (a) PROVED — real, rigorous derivations exist in
approaches/bounds/bounds.md and are reproduced in full in
itemA_proofs.md. The only finite-check component is the integer
minimization itself, which the referee already re-verified and whose
range-sufficiency is now proved (Prop. A11). NO (c) items in Item A.
Once itemA_proofs.md is transcribed into the paper (or bounds.md is
attached as an appendix/companion), the referee's objection "asserted,
not proved" is fully discharged FOR LEMMA 3.4. (Items B and C are owned
by sibling agents and are not covered by this verdict.)
