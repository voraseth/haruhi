# Item B audit — Algorithm 2 rejection rules R1–R14
Agent: T-n6-auditB. Status file; appended incrementally (drop-resistant protocol).

## Classification table
| Rule | Verdict | Source | Dependencies | Control check |
|------|---------|--------|--------------|---------------|
| R1  | (a) PROVED | UNIT-n6, proof6.md par2(h) | T0-n6, PNUM-n6 (L1,L1a), T1-n6 | pass (see logs/itemB_controls.log) |
| R2  | (a) PROVED | T1-n6, proof6.md par2(g) | Prop 1(a)-(f) only | pass |
| R3  | (a) PROVED | T2-n6, proof6.md par2(h) | Prop 1(b) | pass |
| R4  | (a) PROVED | LEMMAS-n6, proof6.md §5 | T0-n6 + gap dichotomy | pass (Q2=0 on 872; 0 on 873s) |
| R5  | (a) PROVED | L12-n6, proof6.md §6 | P0, LEMMAC step 1 (zp2g classification), L2 | pass |
| R6  | (a) PROVED | LU8-n6, proof6.md §6 (Z=0 only, as gated) | P0, T1, L2 | pass |
| R7  | (a) PROVED | DEFSPLIT-n6, proof6.md §6 + algebra | L1 (l<=5) | pass |
| R8  | (a) PROVED | E1-n6, E2-n6, proof6.md §6 | P0, L2 | pass |
| R9  | (a) PROVED | T7-n6 + E1/E2, proof6.md §6 | P0, T1, T2, L1a (hop acyclicity) | pass (equality on 872: NCh=26) |
| R10 | (a)+(b) PROVED given C6-A finite check | LEMMAR-n6 §8; C6-A cert (chain6.c / chains871.c, indep.) | C6-A (finite), P0 | pass |
| R11 | (a) PROVED | E3-n6 + LEMMAC-n6 + Ns<=NCh | E1, E2, L1, L2, P0 | pass (PEN=25=Ncyc on 872) |
| R12 | (a)+(b) PROVED given C6-B finite check | LEMMAA-n6 §8; C6-B cert | C6-B (finite), E1-E3, LEMMAC | pass (equality -21=-21 on 872) |
| R13 | (a)+(b) PROVED given C6-C/C6-S finite checks | PARETO-n6, PARETOS-n6 §8; CHAINRUN-n6 proof871 §4; tables chain6.c + chains871.c (indep.) | C6-B/C/S (finite), E1-E3, LEMMAC, L1, P3 | pass (Fs equality 29 on 872; F equality 24 on 873s) |
| R14 | (a) PROVED | GROUPS-n6, proof871.md §5 | L2, P0, T1, T2, L12-argument | pass |

## Rule statements (from PAPER-n6-872.tex, Appendix A.2, lines 1155-1188)
Derived quantities: P=24+D/5, h=23+D/5+Z-e, Sp=S5+S4, Fp=P-Sp,
cnl=e-(zq+zh+zp2s+zp2g), hits=e-Q2-zp3-zp2g, SH=hits, ST=cnl.
- R1: h >= 0
- R2: cnl >= 0
- R3: hits >= 0
- R4: Q2 <= zp2s + floor(slack/4)   (re-entry bound)
- R5: Ncyc <= e - Q2                (cycle bound)
- R6: at Z=0: D >= e + 5(e - Q2 - Ncyc)   (glue bound)
- R7: max(0, D-4*S4) <= S5 <= D-2*S4; Sp <= D; Sp=0 if D=0  (deficiency split)
- R8: hits <= Sp and cnl <= Sp      (endpoint inequalities)
- R9: NCh <= 1 + X4h + zh + cnl; SH <= NCh; ST <= NCh   (chain count)
- R10: Rcap = 1+X4h+zh+cnl+S4: Fp+S5 <= 4*Rcap and S5 <= 2*Rcap  (run-count caps)
- R11: OV=max(0,SH+ST-Sp), PEN=max(OV, Ncyc-zp2g), PEN <= NCh  (singleton supply)
- R12: P - 2D <= 4*NCh - 2(SH+ST) - PEN   (value ledger)
- R13: P <= F_s(...) and P <= F_C(...)    (Pareto frontiers)
- R14: link-path length multiset packs into Ncomp = P-cnl+Q2+zp3+Ncyc pointer
  components of <=5 vertices, component with m paths carries k>=m-1 nc-runs
  (k>=m if cycle), the k summing to e  (component packing)

## Summary
Counts: (a) PROVED: 10 rules outright (R1-R9, R11, R14 — R10, R12, R13 are
proved reductions resting on finite checks); (b) FINITE-CHECK components with
complete sufficiency arguments: 4 certified tables (C6-A, C6-B, C6-C, C6-S)
feeding R10, R12, R13; (c) NOT PROVED: NONE — zero undischarged items.
Per-rule: R1-R9, R11, R14 = (a); R10, R12, R13 = (a)+(b) (mathematical
reduction proved, terminal fact machine-certified twice independently, with a
proved sufficiency argument that no ordering falls outside the checked range:
the enumeration domain — abstract chains — is a proved SUPERSET of realizable
chains, and beyond the tables' cost range only bounds proved for all costs
are used, so there is no habitat-dependence in the range claim).

Positive controls (checks/itemB_controls.py, logs/itemB_controls.log): the
verified 872 (L=872, e=25, D=25, X4=0, Z=0, corner (25,0,0), measured
Ncyc=25, S5=25, NCh=26) and ALL 96 verified 873s (L=873, e=0, D=0, X4=6,
NCh=6) pass ALL 14 rules at their own lengths — CONTROL PASS, 0 rejections
over 97 objects x 14 rules. Many with equality (R6, R8, R9 on the 872; R10,
R12, R13 on the 873s), i.e. the rules are tight against real objects, not
vacuously loose.
Discrimination control (by direct computation): the 872's profile with Ncyc
perturbed 25 -> 24 violates R6 (25 >= 25 + 5*1 fails) and with NCh 26 -> 25
violates R9's equality partner R11+R12 chain; the rules do reject near-miss
profiles. The published maps (868/869/870 empty) are the systemic
discrimination evidence, reproduced byte-for-byte by the independent
reimplementation scan871.py (proof871.md §7 REGRESSION).

Scanner gating verified in source: R6 applied only at Z=0
(scan871.py:662, `'lu8' in on and Z == 0`), matching LU8-n6's hypothesis.

Dependency DAG: acyclic and grounded (itemB_proofs.md, final section). The
one circularity risk (L12 <-> LEMMAC) is benign: L12 uses only LEMMAC's
Step-1 edge classification, which is independent of L12.

VERDICT ON ALGORITHM 2's COMPLETENESS: with the proofs transcribed in
itemB_proofs.md, every rejection test R1-R14 is a mathematical theorem
quantified over ALL first-occurrence orderings (not only surviving or special
cases), each derived from the raw n=6 definitions plus previously proved
results, with all finite components exhaustively certified by two independent
implementations over a proved-sufficient range. The enumeration ranges of
Algorithm 2 are forced by the proved identities (UNIT/THMM/PNUM + h>=0 +
R4/R5/R9 caps), so no profile of a real ordering escapes the scan. Algorithm
2's completeness for its claim — emptiness at 868-870 and the sixteen classes
at 871 — IS ESTABLISHED, conditional only on the separately registered
premise P1-n6 (L(6) >= 868) which is outside this item's scope.
