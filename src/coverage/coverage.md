# coverage.md — THE COVERAGE THEOREM for the L = 871 emptiness proof

T-n6-coverage, 2026-09-03.  Workdir `approaches/n6coverage/`.

## 0. What this document answers

The referee's objection, accepted by the coordinator:

> the proof's weight rests on the bridge "all possible length-871 candidates"
> --> "exactly these 631 computational instances", and that bridge is NOT
> independently auditable from the manuscript.  If even one census
> configuration or one closure topology is omitted, the 1,111 exhaustive
> searches prove nothing.

This document supplies:

1. **The Coverage Theorem** (sect. 6), with a proof in which every step is a
   lemma proved from raw definitions or a registered theorem, and every step
   that rests on an enumeration is (a) specified as an algorithm, (b) proved to
   over-approximate, and (c) exhibited as printed data.
2. **The census generator specified as an algorithm** (sect. 3), to the standard
   of Algorithm 2's R1–R14 audit (`approaches/n6audit/itemB_proofs.md`), with a
   necessity proof for every one of its eleven tests (sect. 4).
3. **The printed data**: all 200 configurations and all 631 instances, from a
   committed one-command script (sect. 7).  52.5 KB / 5.0 KB gzipped.
4. **The resolution of Lemma 6.8's two-loop bound** (sect. 5): it is now a
   **PROVED MATHEMATICAL BOUND**, not a computational fact read off the census.
5. **Controls and discrimination** (sect. 8).

Headline: **the Coverage Theorem is PROVED, with no residual audited-output
step.**  Every link of the bridge is closed by hand proof or by exact machine
set-equality; the only machine-borne content left is the computer-assisted core
the result is entitled to (the 1111 exhaustive searches).  In particular the
two-loop bound — the referee's sharpest sub-point — is proved mathematically
(sect. 5.2), and the clauses `c_2 = 0` and `a_3 = 0`, which this document
originally recorded as audited outputs, are now a finite case analysis with
printed arithmetic (sect. 6.4), following T-n6-fin's derivation which I have
verified independently.

## 1. Notation and standing facts

Raw n = 6 definitions as in `approaches/n6audit/itemB_proofs.md` §Preliminaries:
720 permutations of [6]; `rot`, `sig`, `rho(p) = p[1:5] p[0] p[5]`;
d(p,q) = 6 − |longest suffix of p that is a prefix of q|; 120 rotation classes;
`rho` of order exactly 5, hence 144 `rho`-orbits; a first-occurrence ordering
q_1..q_720 of a superpermutation; *runs* = maximal d = 1 blocks; e = #runs − 120;
y_C = temporally last member of class C; crit(C) = rot(y_C); the transition
typing and the pools zq, zh, zp3, zp2s, zp2g of proof6.md §1.  Facts F1–F4 and
P0–P4 are as in that file.

For a hypothetical length-871 superpermutation, slack = 0 and W = 146, so
(Lemma of identities) D/5 + X4 + Z = 4, and Theorem 5.7 (registered THEOREM
N871-B, reviewed R-n6-4) leaves exactly **sixteen structural classes**:

| corner (D,X4,Z) | e values | X4h | count |
|---|---|---|---|
| (20,0,0) | 1,2,3,4,5,6,7,8,9 | 0 | 9 |
| (15,1,0) | 1,2,3,4,7 | 1 | 5 |
| (10,2,0) | 2 | 2 | 1 (X4h = 1 killed by THEOREM K1) |
| (15,0,1) | 2 | 0 | 1 (the *defect* class; Z = 1) |

Component vocabulary (TC2, proof_tight.md §4).  The *pointer graph* has one
vertex per run; its components are directed paths or cycles of at most five
vertices (P4/L2).  At Z = 0 each component alternates crit-chains and single
non-critical ("nc") runs.  Write

* a_m = number of **path** components with m link-paths (m = 1,2,3),
* c_m = number of **cycle** components with m link-paths (m = 1,2),
* a_1 = one-block components ("arcs"), a_2 = two-block components ("spans"),
* n5, n4 = number of one-block components of link-path length 5, 4;
  nS = number with length <= 3; n45 = n5 + n4; a_1 = n45 + nS,
* P# = 24 + D/5 = total number of link-paths; NCh = e + 1 + X4h = number of
  hop-chains (TC1),
* b_q1 = 1 iff q_1's pointer component has m >= 2,
* LAM = a_2 + a_3 + 1 + X4h − b_q1 = number of chains that are not forced
  singletons (TC4),
* Delta_1 = sum over one-block components of (5 − l) = their total deficiency.

Standing identities, all proved in proof_tight.md §4–§5 and re-derived here in
sect. 4:

    (I-a)  a_1 + a_2 + a_3 = P# − e
    (I-b)  a_2 + 2 a_3 + c_1 + 2 c_2 = e
    (I-c)  D = 5 P# − 120  (equivalently P# = 24 + D/5)
    (I-d)  120 = sum of all link-path lengths

## 2. The chain that must be covered

    hypothetical 871
      |  (S1) Theorem 5.7 / N871-B
      v
    one of 16 structural classes  (D, X4, Z, e, X4h)
      |  (S2) the CENSUS GENERATOR, Algorithm G
      v
    one of 200 configurations (Z = 0) or one of 2 wirings (Z = 1)
      |  (S3) the EXPANSION, Algorithm E
      v
    one of 631 search instances (piece multisets)
      |  (S4) the GEOMETRIC MODEL M
      v
    a placement of the instance's pieces on the 144 rho-orbits
      |  (S5) the CLOSURE TOPOLOGY (Lemma 6.8)
      v
    linear closure, or one of the loop closures  ->  one of 1111 runs
      |  (S6) all 1111 runs returned UNSAT EXHAUSTED
      v
    contradiction

Steps S1, S4, S6 are already registered and independently reviewed (S1:
R-n6-4; S4: R-n6-7 §2.1, clause-by-clause machine check on the verified 872;
S6: R-n6-7 §4 + R-n6-9, with node-identical independent replication).  This
document closes S2, S3 and S5, which is exactly the referee's bridge.

## 3. ALGORITHM G — the census generator, fully specified

Implementation: `checks/census_gen.py::gen_cell` (this workdir, written from
this specification, not from the artifact's code).  Artifact's implementation:
`approaches/n6tight/checks/tight_enum.py::enumerate_cell`.  The two range over
*different* search spaces (see sect. 7.2) and are proved to agree.

**Input.**  A structural class: (D, X4, Z = 0, e, X4h).

**Output.**  A finite set of *configurations*, each a tuple

    (a_2, a_3, c_1, c_2, b_q1, n45, n4, sum_c1, sum_c2)

where sum_c1, sum_c2 are the total link-path lengths carried by the c_1 and
c_2 cycles.

**Enumeration ranges and tests.**  P := 24 + D/5.

    G1.  P := 24 + D/5.                                     [identity (I-c)]
    G2.  for a_2 = 0 .. e:
         for a_3 = 0 .. floor((e − a_2)/2):
         for c_2 = 0 .. floor((e − a_2 − 2 a_3)/2):
             c_1 := e − a_2 − 2 a_3 − 2 c_2;  reject if c_1 < 0.   [(I-b)]
    G3.  a_1 := P − e − a_2 − a_3;  reject if a_1 < 0.            [(I-a)]
    G4.  sum_c1 := 4 c_1,  sum_c2 := 3 c_2.                       [TC2c]
    G5.  sum over three-block components of lengths := 3 a_3.     [TC2 caps]
    G6.  for b_q1 in {0,1}, restricted to {0} unless a_2 + a_3 >= 1.
    G7.  LAM := a_2 + a_3 + 1 + X4h − b_q1;
         sh_rest := a_2 + a_3;  st_rest := max(0, a_2 + a_3 − b_q1);
         blocks_rest := a_1 + 2 a_2 + 2 a_3 − b_q1.                [TC1/TC3/TC4]
    G8.  for n5 = 0 .. a_1, for n4 = 0 .. a_1 − n5:
             nS := a_1 − n5 − n4;  n45 := n5 + n4;  Rmax := nS + LAM;
             REJECT if n45 > 4 Rmax  or  n4 > 2 Rmax
                    or  max(ceil(n45/4), ceil(n4/2)) > Rmax.       [C6-A + TC4]
    G9.  rem := 120 − 5 n5 − 4 n4 − 3 a_3 − sum_c1 − sum_c2;
         REJECT unless  nS + 2 a_2  <=  rem  <=  3 nS + 4 a_2.     [(I-d) + TC2]
    G10. V := P − 2 D;
         v_sing := (2 sum_c1 − 9 c_1) + (2 sum_c2 − 18 c_2) − 7 a_3 − 3 b_q1;
         REJECT if  V > v_sing + 4 LAM − 2 sh_rest − 2 st_rest.    [C6-B value ledger]
    G11. cost_sing := (5 c_1 − sum_c1) + (10 c_2 − sum_c2) + 4 a_3 + 2 b_q1;
         cost_rest := D − cost_sing;  REJECT if cost_rest < 0;
         REJECT if blocks_rest > F(LAM, cost_rest, sh_rest, st_rest).
                                                                   [C6-B/C6-C Pareto ledger]
    G12. emit (a_2, a_3, c_1, c_2, b_q1, n45, n4, sum_c1, sum_c2).

F is the certified chain-capacity function of Appendix B (`checks/pareto.py`,
re-implemented here from the lemma statement; it reproduces every value quoted
in proof_tight.md §7: F(2,8,0,0)=20, F(2,15,2,0)=F(2,15,1,1)=25, F(3,15,2,1)=30,
F(2,14,1,0)=25, F(2,12,1,0)=F(2,13,2,0)=23, F(1,13,0,0)=19).

## 3b. ALGORITHM E — the expansion to instances

**Input.** one configuration record of Algorithm G, carrying additionally
n5, n4, nS and `rem`.

    E1.  for every multiset {s2_1..s2_{a_2}} with each s2_i in {2,3,4}:
    E2.      sigma := rem − sum(s2_i);  skip if sigma < 0;
    E3.      for every multiset of nS values in {1,2,3} summing to sigma,
             written (n3, n2, n1) by value:
    E4.          emit instance (n5, n4, n3, n2, n1, c_1, {s2_i}, b_q1).

The engine itself ranges over the (l_1, l_2) split of each span (l_1+l_2 = s2)
and over all placements; E does not need to.

**The Z = 1 defect class** is not enumerated by G.  THEOREM K2 (proof_tight.md
§7; machine part `checks/z1_corner.py`) proves that at (15,0,1), e = 2 the
component skeleton is pinned to exactly two wirings — zh: A = [P nc P'] with
l_P + l_P' = sA <= 4 and B = [ncH P''] with l_B <= 4, plus 24 one-block
components and no cycles; zp3: B1 = [P1 nc P2] with sA <= 4 and B2 = [P3 nc]
with l_B <= 4, same remainder.  Its expansion is:

    Z1.  for sA in {2,3,4}, for l_B in {1,2,3,4}:
    Z2.      budget := sA + l_B                      [see Lemma 4.12 below]
    Z3.      for every multiset of one-block deficiencies (1 for length 4,
             2,3,4 for lengths 3,2,1) summing to `budget`, with
             n5 := 24 − (number of them) >= 0:
    Z4.          emit instance (n5, n4, n3, n2, n1, sA, l_B) for each of the
                 two wirings.

No run-cap, value or Pareto test is applied in Z1–Z4: the defect-class
instance list is a strictly coarser over-approximation than G's, which is safe
(sect. 4, Remark).

## 4. Over-approximation: every test of G and E is proved NECESSARY

The format follows `approaches/n6audit/itemB_proofs.md`: statement, proof from
raw definitions or from a named proved theorem, dependency list, and a control
value on the real objects.

Throughout, SIGMA is an arbitrary length-871 superpermutation on {1..6} whose
structural class is (D, X4, 0, e, X4h); "the ordering" is its first-occurrence
ordering; all component quantities are read off the ordering as defined in
sect. 1.  Since slack = 0 forces Q2 = zp2s = 0 and Z = 0 forces
zq = zh = zp3 = zp2g = 0, TC1–TC4 all apply to SIGMA.

**Lemma 4.1 (G1).**  P# = 24 + D/5, and in particular 5 | D.
*Proof.*  P3 of itemB_proofs.md: along a link-path crit(v_{i+1}) = rho(crit(v_i)),
`rho` has order 5, so every link-path has length l <= 5; the link relation is
acyclic, so the 120 classes partition into P# link-paths; D := sum(5 − l) over
paths = 5 P# − 120.  QED.  *Deps:* P0, P3.  *Control:* the verified 872 has
D = 25, P# = 29 = 24 + 5 (`myanalyze.py` output, logs/controls.log).

**Lemma 4.2 (G2, identity (I-b)).**  a_2 + 2 a_3 + c_1 + 2 c_2 = e, and each
of a_2, a_3, c_1, c_2 is >= 0.
*Proof.*  By TC2 the pointer components alternate crit-chains and *single* nc
runs, with a path component of m link-paths carrying exactly m − 1 nc runs and
a cycle of m link-paths carrying exactly m.  TC2 also gives m <= 3 for path
components and m <= 2 for cycles.  Summing over components, the total number
of nc runs is (a_2 + 2 a_3) + (c_1 + 2 c_2).  By P0(c) the number of nc run
starts is exactly e.  QED.  *Deps:* P0(c), P4/L2, TC2.  *Control:* 872:
0 + 0 + 25 + 0 = 25 = e.  Counterexample object #11 (L=880): 5 + 0 + 25 + 0
= 30 = e.  Both verified in `checks/controls.py`.

**Lemma 4.3 (G2 ranges).**  The loop bounds a_2 <= e, a_3 <= (e − a_2)/2,
c_2 <= (e − a_2 − 2 a_3)/2 reject no real ordering.
*Proof.*  Immediate from Lemma 4.2 and non-negativity of the remaining terms.
QED.

**Lemma 4.4 (G3, identity (I-a)).**  a_1 + a_2 + a_3 = P# − e, hence
a_1 = P# − e − a_2 − a_3 >= 0.
*Proof.*  Each link-path lies in exactly one pointer component (GROUPS(ii),
re-derived in TC2's proof: a crit-chain of a path of length l occupies exactly
l pointer vertices).  Counting link-paths by component:
P# = a_1 + 2 a_2 + 3 a_3 + c_1 + 2 c_2.  Subtracting Lemma 4.2 gives
P# − e = a_1 + a_2 + a_3.  QED.  *Deps:* TC2, P3.  *Control:* 872:
4 + 0 + 0 = 4 = 29 − 25.

**Lemma 4.5 (G4 = TC2c).**  Every pointer cycle has exactly five vertices;
hence at Z = 0 an m = 1 cycle has link-path length exactly 4 and an m = 2 cycle
has l_1 + l_2 = 3 exactly.  So sum_c1 = 4 c_1 and sum_c2 = 3 c_2.
*Proof.*  Registered TC2c (proof_tight.md §4, delta-reviewed SOUND by R-n6-6):
along a pointer cycle the run starts advance by `rho` (P4) and close up, so
rho^k(s) = s for a k-vertex cycle; `rho` has order exactly 5 on all 720
permutations (registered `blockcheck`), so k = 5; TC2's alternation gives
sum l_j + m = 5.  QED.  *Deps:* P4, TC2, order(rho) = 5.  *Control:* 872 has
25 cycles, all of link-path length 4, sum_c1 = 100 (controls.log).

**Lemma 4.6 (G5).**  A three-block path component has l_1 + l_2 + l_3 = 3
exactly, i.e. all three link-paths are singletons.
*Proof.*  TC2 gives sum_j l_j <= 6 − m = 3 for m = 3, and each l_j >= 1.  QED.
*Deps:* TC2, P4/L2.

**Lemma 4.7 (G6).**  b_q1 = 1 is possible only if a_2 + a_3 >= 1.
*Proof.*  b_q1 = 1 means q_1's pointer component has m >= 2 link-paths, and by
F3 (q_1's run start is a component source) that component is a *path*
component, hence counted by a_2 or a_3.  QED.  *Deps:* F3, TC2(a).

**Lemma 4.8 (G7).**  NCh = e + 1 + X4h; the number of forced-singleton chains
is exactly (c_1 + 2 c_2) + a_3 + b_q1; hence the number LAM of chains that are
not forced singletons is a_2 + a_3 + 1 + X4h − b_q1, and the number of
link-paths those chains must carry is blocks_rest = a_1 + 2 a_2 + 2 a_3 − b_q1
(all link-paths, minus the forced singletons).
*Proof.*  TC1 gives NCh = e + 1 + X4h exactly.  TC3.3 makes every cycle
link-path a singleton chain (c_1 + 2 c_2 of them); TC3.4 makes the middle
link-path of every three-block component a singleton chain (a_3); TC3.5 makes
q_1's link-path a singleton chain when b_q1 = 1.  These are pairwise distinct
chains.  Subtracting from NCh and using Lemma 4.2 gives LAM as stated.  The
block count: total link-paths P# = a_1 + 2 a_2 + 3 a_3 + c_1 + 2 c_2 minus the
forced singletons (c_1 + 2 c_2) + a_3 + b_q1.  QED.  *Deps:* TC1, TC1-end,
TC3.  *Control:* 872: NCh = 26 = 25 + 1 + 0, forced singletons = 25 cycle
paths, LAM = 1, blocks_rest = 4 — the registered decomposition.

**Lemma 4.9 (G8, the run caps).**  Let R be the number of maximal runs of
consecutive length-{4,5} link-paths inside chains.  Then
R <= nS + LAM, n45 <= 4 R and n4 <= 2 R.  Consequently, with
Rmax := nS + LAM, the rejections `n45 > 4 Rmax`, `n4 > 2 Rmax` and
`max(ceil(n45/4), ceil(n4/2)) > Rmax` reject no real ordering.
*Proof.*  This is TC4 verbatim (proof_tight.md §5): a link-path of length 4 or
5 is either the single path of a one-block path component or a cycle-four; a
cycle-four is a singleton chain (TC3.3), so the {4,5} paths appearing inside
non-singleton chains are exactly one-block-component paths, counted by n45.
Inside a chain, consecutive {4,5} paths are separated only by one-block-component
paths of length <= 3 (TC3.6: interior paths of a chain are one-block paths;
chain-endpoint paths belonging to m >= 2 components have length <= 3 by the TC2
caps).  Hence each of the LAM non-singleton chains contributes at most
(number of short one-block paths inside it) + 1 maximal {4,5}-runs; summing,
R <= nS + LAM.  The per-run caps n45 <= 4R and n4 <= 2R are C6-A (registered
n = 6 chain constants: run cap 4, at most two fours, certified independently
from all 720 head crits), applied to each maximal run — legitimate because a
contiguous subsequence of a chain is a chain.  Finally
`max(ceil(n45/4), ceil(n4/2)) <= R` is the same pair of inequalities restated.
QED.  *Deps:* TC2, TC3.3, TC3.6, TC4, C6-A.  *Control:* 872: n45 = 4, n4 = 0,
nS = 0, LAM = 1, R = 1 <= 1 and 4 <= 4.  873 baseline: n45 = 24, nS = 0,
LAM = 6, R = 6, 24 <= 24 — TIGHT on a real object, so the cap is exactly right
and not slack.

**Lemma 4.10 (G9, the class budget).**  Let Sigma_S be the total length of the
short one-block components and Sigma_2 the total of the s2 values.  Then
5 n5 + 4 n4 + Sigma_S + Sigma_2 + 3 a_3 + sum_c1 + sum_c2 = 120, and
nS <= Sigma_S <= 3 nS, 2 a_2 <= Sigma_2 <= 4 a_2.  Hence the rejection
`not (nS + 2 a_2 <= rem <= 3 nS + 4 a_2)` with
rem = 120 − 5 n5 − 4 n4 − 3 a_3 − sum_c1 − sum_c2 rejects no real ordering.
*Proof.*  The 120 rotation classes are partitioned by the link-paths (P3), and
each link-path lies in exactly one component, so the total of all link-path
lengths is 120 — this is identity (I-d).  Grouping by component type gives the
displayed equation.  The ranges: a short one-block component has length in
{1,2,3}; a two-block component has s2 = l_1 + l_2 with each l_i >= 1 and
sum <= 6 − 2 = 4 (TC2), so s2 in {2,3,4}.  QED.  *Deps:* P3, TC2.
*Control:* 872: 5·4 + 0 + 0 + 0 + 0 + 100 + 0 = 120.

**Lemma 4.11 (G10 and G11, the two ledgers).**  Write, for a chain
c = (its total deficiency cost), a = [its first link-path is short], b = [its
last is short].  Then (i) the number of link-paths in that chain is at most
g(c, a, b), the certified frontier of Appendix B, and (ii) summing over the
LAM non-singleton chains, blocks_rest <= F(LAM, cost_rest, sh_rest, st_rest)
where cost_rest = D − cost_sing is the deficiency left after the forced
singletons take their exact values, sh_rest = a_2 + a_3 and
st_rest = max(0, a_2 + a_3 − b_q1) are the numbers of non-singleton chains
forced to begin / end with a short link-path.  Test G11 rejects exactly the
violations of (ii).  Test G10 is the coarser C6-B linear form of the same
statement.
*Proof.*  (i) is the certified chain Pareto frontier (proof_tight.md §6,
re-certified from scratch by `chainpareto.c`, and equal entry-for-entry to the
registered C6-C table; rows 17–20 use the certified g(20) = 25, rows > 20 the
proved C6-B bound 4 − 2a − 2b + 2c).  (ii) The forced singletons' costs are
exact: a cycle-four costs 5 − 4 = 1 each (Lemma 4.5), an m = 2 cycle's two
paths cost 10 − 3 = 7 (Lemma 4.5), a three-block component's middle path costs
5 − 1 = 4 (Lemma 4.6 gives all three lengths 1; the middle one is the forced
singleton, and the ledger charges the whole component's non-host cost
4 a_3), and q_1's forced singleton when b_q1 = 1 costs 5 − l with l <= 3, i.e.
at least 2.  cost_sing collects exactly these; the remainder cost_rest is
available to the LAM host chains.  sh_rest / st_rest: by TC3.1 every link-path
at position >= 2 of a path component heads its chain, and by the TC2 caps such
a path has length <= 7 − 2m <= 3, i.e. is short; there are a_2 + a_3 of them
that are not forced singletons (the closers of two-block components and the
last paths of three-block components).  Dually TC3.2 makes every path at
position <= m−1 a chain ender, and those are short as well, except that when
b_q1 = 1 one of them is q_1's own forced singleton, whence the −b_q1.  Since F
is by construction the maximum of sum_i g(c_i, a_i, b_i) over all splittings of
cost_rest into LAM chains with at least sh_rest short-headed and st_rest
short-tailed, blocks_rest <= F(...) holds for the real ordering.  QED.
*Deps:* C6-B, C6-C, the certified frontier, TC2, TC3.1–3.5, Lemmas 4.5, 4.6,
4.8.  *Control:* 872: LAM = 1, cost_rest = 25 − 25·1 = 0, blocks_rest = 4,
F(1,0,0,0) = g(0,0,0) = 4 >= 4 — TIGHT.  873: LAM = 6, cost_rest = 0,
blocks_rest = 24, F(6,0,0,0) = 24 >= 24 — TIGHT.  Both real objects sit exactly
on the frontier, so the ledger is calibrated, not loose.

**Lemma 4.12 (E1–E4, and Z1–Z4).**  (E) Every real ordering in the class whose
configuration is gamma has, as its concrete piece multiset, exactly one of the
instances E(gamma): the s2 multiset is the multiset of two-block component
totals (each in {2,3,4} by Lemma 4.10) and (n3,n2,n1) is the multiset of short
one-block lengths, and by Lemma 4.10 these two multisets sum to `rem`.  The
enumeration E1–E3 ranges over *all* such pairs, so no real ordering's instance
is omitted.  (Z) In the defect class, the components are pinned by K2 to the
two listed wirings; the deficiency identity reads
D = 15 = (10 − sA) + (5 − l_B) + Delta_1 with c_1 = c_2 = 0, so
Delta_1 = sA + l_B: the loop Z1–Z3 ranges over all (sA, l_B) in the K2 ranges
and all deficiency multisets of the 24 one-block components summing to
Delta_1, hence over every real defect-class ordering's instance.
*Proof.*  Both are enumerations of *all* multisets consistent with proved
identities, with no test applied; nothing is rejected.  QED.

**Remark (over-approximation is monotone).**  G and E only ever *reject*; each
rejection is licensed by one of Lemmas 4.1–4.12.  Therefore the emitted set is
a superset of the set of configurations/instances that real length-871
orderings realise.  Omitting a test (as in Z1–Z4) enlarges the output and is
therefore safe for coverage; adding an unproved test would be unsafe, and none
is present.  This is verified as an ablation in sect. 8.3: with all four
non-identity tests disabled the census grows 200 -> 6513 and every one of the
200 survives, confirming the filters are monotone.

## 5. THE TWO-LOOP BOUND — now a theorem, not a measurement

The referee's sharpest sub-point: Lemma 6.8 of the manuscript says "in every
configuration of the census at most two such arcs exist", which is a
*computational* fact standing where a *mathematical* bound is needed, because
Algorithm 6 searches at most two loops **because of** it.

Status of the prior work.  R-n6-7 §2.4 (sustained by R-n6-9) proves the
*structure* — closure graph = one path plus disjoint loops, and every loop
contains at least one two-block-component arc or defect arc — but its final
step reads "the number of disjoint cycles is at most #(M2 pieces not q1's) +
#(B pieces) <= 2", and the "<= 2" there is *asserted from the census*, exactly
as in the manuscript.  **So no, R-n6-7's theorem did not already prove the
bound; the referee is right.**  This section supplies the proof.

### 5.1 The closure graph, precisely

**Definition.**  A chain is a maximal sequence of link-paths joined by hops
(TC1).  By TC3.3 every cycle link-path is a singleton chain; call those *cycle
chains*, and call the others *free chains* (their link-paths all lie in path
components).  The *closure graph* CG has the free chains as vertices, and an
arc A -> B whenever the ordering-transition that ends chain A is the same
transition that enters the head of chain B, or (for a two-block or three-block
component) whenever A's ender emits the CNL into the nc run whose ps-hit enters
B's head.

**Lemma 5.1 (arc inventory).**  At Z = 0 the arcs of CG are exactly:
  (i) one arc per nc run of a *path* component — there are a_2 + 2 a_3 of these
      ("span arcs");
  (ii) one arc per d >= 4 heavy — there are X4h of these ("d4 arcs");
and in the defect class one further "defect arc".  In particular, at Z = 0,
|V(CG)| = a_2 + 2 a_3 + 1 + X4h and |E(CG)| = a_2 + 2 a_3 + X4h = |V| − 1;
in the defect class both sides gain 1 (V = NCh = 3 by TC1z, E = 2), so
|E| = |V| − 1 there too.
*Proof.*  By TC1-end the NCh = e + 1 + X4h chain heads are exactly: q_1's path
(entered by nothing), the e ps-hit-entered heads, and the X4h heads entered by
a d >= 4 heavy; dually the enders are the e CNL-emitting paths, the global-end
path, and the X4h d >= 4-emitting enders.  Each of the e ps-hits is generated by
exactly one nc run (TC2(b): the nc run's out-edge is the premature-sig exit of
z = rot^{-1}(u)), and each of the e CNLs enters exactly one nc run (TC2(a)).
Of the e nc runs, c_1 + 2 c_2 lie in cycles (Lemma 4.2); for those, both the
emitting and the entered link-path are cycle paths, hence cycle chains, hence
*not* vertices of CG.  The remaining a_2 + 2 a_3 nc runs lie in path
components and give arcs between free chains.  Vertex count:
|V| = NCh − (c_1 + 2 c_2) = (e + 1 + X4h) − (c_1 + 2 c_2) = a_2 + 2 a_3 + 1 + X4h
by Lemma 4.2.  QED.  *Deps:* TC1, TC1-end, TC2(a),(b), TC3.3, Lemma 4.2.

**Lemma 5.2 (shape).**  CG has in-degree <= 1 and out-degree <= 1 at every
vertex, a unique source (q_1's chain) and a unique sink (the global-end chain);
hence CG is one directed path from the source to the sink together with
vertex-disjoint directed cycles ("closure loops").
*Proof.*  F1 gives each run start at most one entering transition, so each
chain head has at most one in-arc; each chain ender has exactly one completion
exit (or none, at the global end), so at most one out-arc.  By TC1-end the only
head with no in-arc is q_1's and the only ender with no out-arc is the global
end's.  A functional digraph with |E| = |V| − 1 (Lemma 5.1) decomposes into
|V| − |E| = 1 path plus cycles.  QED.  *Deps:* F1, F3, TC1-end, Lemma 5.1.

**Lemma 5.3 (d4 arcs are temporally immediate).**  Define t(A) := the
ordering position of y_{C} for C the last class of chain A's last link-path.
If A -> B is a d4 arc then t(A) < t(B).  Consequently no closure loop consists
of d4 arcs only.
*Proof.*  A d4 arc is a single transition: A's ender's completion exit at
position t(A) lands at position t(A) + 1 on crit(C') = rot(y_{C'}) for C' the
head class of B's first link-path (TC1-end).  Since rot(y_{C'}) is a member of
C' and y_{C'} is the temporally *last* member of C', pos(y_{C'}) > t(A) + 1.
Along a link-path pos(y) strictly increases (P3), and along a chain the hops
strictly increase pos(y) by the same argument, so
t(B) >= pos(y_{C'}) > t(A).  A cycle of d4 arcs would give t(A) < t(A).  QED.
*Deps:* P0(a), P3, TC1-end.

**Corollary 5.4.**  The number of closure loops is at most
U := a_2 + 2 a_3 (+1 for the defect arc in the Z = 1 class).
*Proof.*  Loops are vertex-disjoint (Lemma 5.2), hence arc-disjoint; each
contains at least one non-d4 arc (Lemma 5.3), and by Lemma 5.1 there are
exactly U of those.  QED.

### 5.2 THEOREM (two-loop bound).  U <= 2 in every one of the sixteen classes.

Hence every hypothetical length-871 candidate's closure structure is the linear
path plus **at most two** closure loops.

*Proof.*  **Step 0 (deficiency accounting).**  By Lemma 4.1,
D = sum over all link-paths of (5 − l).  Group by component and use the TC2 /
TC2c caps: a one-block component contributes 5 − l >= 0, summing to Delta_1; a
two-block component contributes 10 − s2 >= 6 (Lemma 4.10: s2 <= 4); a
three-block component contributes 15 − 3 = 12 (Lemma 4.6); an m = 1 cycle
contributes 1 and an m = 2 cycle 7 (Lemma 4.5 — or, without TC2c, >= 1 and
>= 7 from the L2 five-vertex cap alone).  Hence

    D  >=  Delta_1 + 6 a_2 + 12 a_3 + c_1 + 7 c_2 .

Substituting c_1 = e − a_2 − 2 a_3 − 2 c_2 (Lemma 4.2):

    D  >=  Delta_1 + 5 a_2 + 10 a_3 + 5 c_2 + e ,

that is, writing Lambda := a_2 + 2 a_3 + c_2,

    (*)   5 Lambda  <=  D − e − Delta_1  <=  D − e .

Since U = a_2 + 2 a_3 <= Lambda, (*) already bounds U.

**Step 1 (the classes where (*) suffices).**
* (10,2,0), e = 2:   5 Lambda <= 8,  so Lambda <= 1 and **U <= 1**.
* (15,1,0), e in {1,2,3,4,7}:  5 Lambda <= 15 − e <= 14, so **U <= 2**.
* (20,0,0), e >= 6:  5 Lambda <= 20 − e <= 14, so **U <= 2**.
* (20,0,0), e in {1,2}: c_1 >= 0 in Lemma 4.2 gives e >= a_2 + 2 a_3 = U, so
  **U <= 2**.
Only (20,0,0) with e in {3,4,5} remains, where (*) gives only Lambda <= 3.

**Step 2 (the residual cases: U = 3 is refuted by the run cap).**
Suppose (20,0,0), e in {3,4,5}, U = a_2 + 2 a_3 = 3.  Then Lambda <= 3 forces
c_2 = 0, and (a_2, a_3) is (3,0) or (1,1).  From (*),
Delta_1 <= D − e − 5 Lambda = 20 − e − 15 = 5 − e.
Every *short* one-block component (length <= 3) contributes at least 2 to
Delta_1, so nS <= (5 − e)/2.  By Lemma 4.4, a_1 = 28 − e − a_2 − a_3, and
n45 = a_1 − nS.  By Lemma 4.8, LAM = a_2 + a_3 + 1 + X4h − b_q1
= a_2 + a_3 + 1 − b_q1 <= a_2 + a_3 + 1 (X4h = 0 in this corner).  By Lemma 4.9,
n45 <= 4 R <= 4 (nS + LAM).  So a real ordering needs

    a_1 − nS  <=  4 nS + 4 LAM ,   i.e.   a_1 − 4 LAM  <=  5 nS .

Case (a_2,a_3) = (3,0):  LAM <= 4, a_1 = 25 − e, and nS <= (5 − e)/2.
  e = 3: need 22 − 16 = 6 <= 5 nS, i.e. nS >= 2, but nS <= 1.  IMPOSSIBLE.
  e = 4: need 21 − 16 = 5 <= 5 nS, i.e. nS >= 1, but nS <= 0.  IMPOSSIBLE.
  e = 5: need 20 − 16 = 4 <= 5 nS, i.e. nS >= 1, but nS <= 0.  IMPOSSIBLE.
Case (a_2,a_3) = (1,1):  LAM <= 3, a_1 = 26 − e, nS <= (5 − e)/2.
  e = 3: need 23 − 12 = 11 <= 5 nS, i.e. nS >= 3, but nS <= 1.  IMPOSSIBLE.
  e = 4: need 22 − 12 = 10 <= 5 nS, i.e. nS >= 2, but nS <= 0.  IMPOSSIBLE.
  e = 5: need 21 − 12 = 9  <= 5 nS, i.e. nS >= 2, but nS <= 0.  IMPOSSIBLE.

**Step 3 (the defect class).**  At (15,0,1), e = 2, THEOREM K2 pins the
component skeleton to two wirings, each with exactly one two-block component
and exactly one defect piece and no cycles.  So the non-d4 arcs number exactly
1 + 1 = 2 and **U = 2**.  (Here U = 2 is attained, not merely bounded.)

In every class U <= 2.  QED.

### 5.3 What this proof uses, and what it does not

Used: Lemmas 4.1, 4.2, 4.4, 4.5/L2, 4.6, 4.8, 4.9, 4.10 — i.e. the identities,
the TC2 component caps, the cycle five-vertex bound, and the C6-A run caps.
**Not used:** the value ledger (G10) and the Pareto ledger (G11); neither the
census generator's output nor any search log enters the proof.

Machine audit of the proof (`checks/loopbound.py`, `logs/loopbound.log`).  A
brute-force enumeration of *all* integer tuples (a_2,a_3,c_1,c_2,b_q1,n5,n4,
n3,n2,n1) admitted by that *weakened* system — identities + TC2c + run caps,
with **both ledgers switched off** — reports max U = 2 over all fifteen Z = 0
classes (and the per-class maxima 1,2,2,2,2,2,1,1,1 / 1,1,1,1,0 / 0).  Repeating
it with TC2c's *equality* also dropped, keeping only the L2 five-vertex cap,
again gives max U = 2.  The script also prints the Step-1/Step-2 certificate
line by line.  So the bound is robust to removing every constraint the proof
does not use.

**Answer to the referee's mandate 4: option (a) is achieved — a mathematical
bound is proved.**  The bound is *tight*: configurations with U = 2 exist in
(20,0,0) at e = 2..6 and U = 2 is attained in the defect class, so no proof can
do better than 2, and Algorithm 6's two-loop budget is exactly right.

## 6. THE COVERAGE THEOREM

### 6.1 Statement

> **THEOREM (Coverage).**  Let SIGMA be any superpermutation on {1,...,6} of
> length 871, with first-occurrence ordering q_1..q_720.  Then there exist
>
>  (a) a structural class kappa among the sixteen of Theorem 5.7,
>  (b) a configuration gamma in G(kappa) (or, for kappa the defect class, one
>      of K2's two wirings),
>  (c) an instance iota in E(gamma), one of the 631,
>  (d) a mode m in {0,1} such that the run (iota, m) is one of the 1111
>      committed runs,
>
> such that, after normalising SIGMA by a relabelling of the alphabet, the
> geometric placement that SIGMA induces on the 144 rho-orbits is a *witness*
> accepted by the run (iota, m).
>
> **Corollary.**  Since all 1111 committed runs terminated with the verdict
> UNSAT EXHAUSTED and no node cap was ever reached, no such SIGMA exists;
> L(6) >= 872.

### 6.2 Proof

**(a) SIGMA has a class.**  L = 871 gives slack = 0 and W = 146; by the
identity lemma D/5 + X4 + Z = 4 and by Theorem 5.7 / registered THEOREM
N871-B (reviewed R-n6-4, all 61 map rows reproduced byte-identically by an
independent scanner with the dominance shortcut and search budget removed)
SIGMA's profile (D, X4, Z, e, X4h) is one of the sixteen listed in sect. 1.
Also slack = 0 gives Q2 = zp2s = 0, so at Z = 0 all of TC1, TC1-end, TC2, TC2c,
TC3, TC4 apply to SIGMA; at Z = 1 (the defect class) TC1z and THEOREM K2 apply.

**(b) SIGMA's configuration is in the census.**  Read off SIGMA's ordering the
tuple gamma(SIGMA) = (a_2, a_3, c_1, c_2, b_q1, n45, n4, sum_c1, sum_c2) as
defined in sect. 1.  Every quantity is well defined (the pointer components and
their link-paths are determined by the ordering).  By Lemmas 4.1–4.11, gamma
satisfies every test G1–G11 of Algorithm G.  Since Algorithm G *enumerates* the
full ranges G2, G6, G8 and *emits* everything not rejected, gamma(SIGMA) is in
G(kappa).  For kappa the defect class, THEOREM K2 places SIGMA in one of the
two wirings.

**(c) SIGMA's instance is in the expansion.**  Read off the multiset of
two-block totals {s2_i} and the multiset of short one-block lengths.  By
Lemma 4.10 each s2_i is in {2,3,4} and each short length is in {1,2,3}, and the
two multisets sum to `rem`.  Algorithm E enumerates all such pairs
(Lemma 4.12), so SIGMA's instance iota is in E(gamma).  In the defect class,
Lemma 4.12(Z) does the same.  The instance set over all classes is exactly the
631 instances printed in sect. 7.

**(d) SIGMA induces a placement of iota's pieces.**  By TC2 with L2, every
pointer component occupies *consecutive* rho-positions of a single rho-orbit
(P4: each pointer edge advances the run start by rho).  Relabelling acts
transitively on the 720 permutations, so we may normalise.  SIGMA therefore
induces: one arc of l consecutive rho-positions per one-block component; one
span (block, gap, block) per two-block component with the gap at the nc run
(TC2 alternation); one full five-position orbit per cycle, with four critical
runs and one nc run (TC2c); all pieces pairwise position-disjoint (distinct
runs have distinct start permutations) and covering each of the 120 rotation
classes exactly once as a critical run (definition of crit + P0(a)); chains
joined by *exact* d = 3 hops from the ender's completion exit to the head crit,
which has exactly six possible targets, and by d >= 4 joins where X4h > 0
(TC1 / TC1-end); and the cycles placed by exact cover in the endgame, which is
complete because c_2 = 0 (below) makes every cycle a full virgin orbit.  This
is precisely the model M of the manuscript; every clause is one of the
statements just cited, and R-n6-7 §2.1 verified the whole mapping
clause-by-clause on the verified 872 (`map872.py`, ALL PASS).  Hence SIGMA's
placement satisfies every constraint the engine enforces, and the engine
enforces nothing else (Appendix A.6: "There is no other pruning; the engine's
only cutoff is the explicit node cap", which no cited run reached).

**(e) SIGMA's closure structure is searched.**  By Lemmas 5.1–5.3 and
Corollary 5.4, SIGMA's closure graph is one q_1-to-global-end path plus at most
U <= 2 vertex-disjoint loops (Theorem 5.2).  If there are no loops, mode 0
(linear) searches SIGMA's structure.  If there is at least one, mode 1 anchors
one loop-capable piece at 123456 — legitimate because relabelling is transitive
on the 720 permutations and the anchored piece may be taken to be any chosen
one of SIGMA's loop-carrying pieces — searches the loop content with the same
move set, closes the loop by the anchored piece's own entry type (d3 hop, d4
join, fused zp3 launch, or the degenerate immediate self-launch), optionally
anchors a second loop with a free anchor, and then runs the linear remainder
from a free q_1.  By Theorem 5.2 no third loop can exist, so this family is
exhaustive.  Mode 1 is run for exactly the instances that carry a loop-capable
piece (a two-block component or the defect piece); the other
631 − 480 = 151 instances have U = 0 and are provably linear (Corollary 5.4).

**(f) The run exists.**  The 1111 runs are exactly {(iota, 0) : iota in the 631}
union {(iota, 1) : iota loop-capable} (480 of them).  `checks/match_runs.py`
verifies this against the committed `reviews/R-n6-7-workdir/sweep_all.log`:
1111 runs, set-identical to the list derived here, 0 missing, 0 extra,
631 + 480 split confirmed, 0 SAT, 0 CAPPED/TIMEOUT.

**(g) Contradiction.**  The run (iota, m) reported UNSAT EXHAUSTED, i.e. it
proved that no placement of iota's pieces satisfies M under the closure family
searched.  SIGMA's placement is such a placement.  Contradiction.  QED.

### 6.3 What each step rests on

| step | rests on | kind |
|---|---|---|
| (a) class | Theorem 5.7 / N871-B | registered theorem, independently reviewed (R-n6-4) |
| (b) census | Lemmas 4.1–4.11 | hand proofs, this document |
| (b) enumeration is complete | Algorithm G ranges over G2/G6/G8 exhaustively | specification, sect. 3 |
| (c) expansion | Lemma 4.12 | hand proof (no test applied) |
| (d) model | TC1, TC1-end, TC2, TC2c, TC3, TC4, P0–P4 | hand proofs (proof_tight.md), machine-checked on the 872 |
| (d) c_2 = 0 (endgame completeness) | finite case analysis, 150 censuses | **hand proof**, sect. 6.4 |
| (d) a_3 = 0 (no three-block piece in the engine) | finite case analysis, 150 censuses | **hand proof**, sect. 6.4 |
| (e) closure shape | Lemmas 5.1–5.3 | hand proofs, this document |
| (e) at most two loops | Theorem 5.2 | **hand proof**, this document (was a measurement) |
| (f) run list | `checks/match_runs.py` vs the committed log | machine, exact set equality |
| (g) verdicts | 1111 UNSAT EXHAUSTED, node counts replicated | machine, two independent engines |

### 6.4 c_2 = 0 and a_3 = 0: a finite case analysis, not an audited output

**Status (upgraded 2026-09-03).**  This section previously recorded `a_3 = 0`
and `c_2 = 0` — the two clauses the search engine needs, since it has no
three-block piece and its endgame places only full-orbit cycles — as *audited
outputs* of the census generator: true of all 200 emitted configurations,
hence true of every real candidate because G over-approximates, but with no
hand proof.  T-n6-fin (`approaches/n6finlem/finlem.md` sect. 4) has since
produced a **two-tier finite derivation** of both clauses, and I have verified
it independently (`checks/tier_check.py`, `logs/tier_check.log`).  **The
residual is closed: the Coverage Theorem now has no audited-output step.**

**Lemma 6.4.1 (c_2 = 0 and a_3 = 0).**  No length-871 candidate in any of the
sixteen classes has a type-II cycle or a three-block path component.

*Proof.*  The census coordinate (a_2, a_3, c_1, c_2) of a real candidate lies
in the box of Algorithm G's ranges G2/G3 (Lemmas 4.2–4.4).  Over the sixteen
Z = 0 cells of the habitat — including (10,2,0) at both X4h = 1 and X4h = 2,
so the enumeration does not presuppose THEOREM K1 — that box contains exactly
150 censuses with c_2 >= 1 and exactly 150 with a_3 >= 1; together they are
every census with (a_3, c_2) != (0,0).  Two tests suffice.

*Tier 1 (a one-line pinch; no table lookup).*  Eliminate n45 between Lemma 4.10
and Lemma 4.9.  Lemma 4.10 says the 120 rotation classes are the link-path
lengths, and with length <= 5 on the n45 components, <= 3 on the nS = a_1 − n45
ones, <= 4 on two-block components, = 3 on three-block ones, = 4 and = 3 on the
two cycle kinds,

    120 <= 5 n45 + 3 (a_1 − n45) + 4 a_2 + 3 a_3 + 4 c_1 + 3 c_2,
    i.e.  n45 >= N_lo := ceil( (120 − 3 a_1 − 4 a_2 − 3 a_3 − 4 c_1 − 3 c_2) / 2 ).

Lemma 4.9 says n45 <= 4 R with R <= nS + LAM = (a_1 − n45) + LAM, i.e.

    n45 <= N_hi := floor( 4 (a_1 + LAM) / 5 ),   LAM = a_2 + a_3 + 1 + X4h − b_q1.

N_lo does not involve b_q1 and N_hi is maximised at b_q1 = 0, so evaluating at
b_q1 = 0 gives the weakest form of the test.  A census with N_lo > N_hi admits
no value of n45 at all and is therefore empty.  **This kills 140 of the 150
c_2 >= 1 censuses and 148 of the 150 a_3 >= 1 censuses**, one integer
inequality each.

*Tier 2 (one frontier value each).*  For the remaining 10 + 2 censuses the
Pareto test G11 is already decided at census level, because blocks_rest, LAM,
cost_rest, sh_rest and st_rest are functions of (a_2, a_3, c_1, c_2, b_q1)
alone (Lemma 4.8 and sect. 1.2 of the algorithm spec) — no dependence on n45 or
n4.  So one lookup in the certified capacity table finishes each.  The complete
Tier-2 tables (11 rows for c_2, counting both b_q1 values of the one census
where they differ; 4 rows for a_3) are printed in `logs/tier_check.log`.  Two
representative rows, both tight:

    (20,0,0) e=2, (a2,a3,c1,c2,b_q1) = (0,0,0,1,0):
        blocks_rest = 26 > F(1, 13, 0, 0) = g(13) = 19.      DEAD
    (20,0,0) e=2, (a2,a3,c1,c2,b_q1) = (0,1,0,0,0):
        blocks_rest = 27 > F(2, 16, 1, 1) = 26.              DEAD  (margin 1)

Every one of the 12 rows is DEAD.  Hence no real candidate has c_2 >= 1 or
a_3 >= 1.  QED.

**Why this is a proof and not a measurement.**  Every test used is one already
proved necessary for real orderings in sect. 4 — Lemma 4.9 (run caps, via
TC4 + C6-A), Lemma 4.10 (class budget, via P3 + TC2/TC2c) and Lemma 4.11
(Pareto, via the certified frontier).  No test outside Algorithm G is used, and
the *value* ledger G10 is not used at all, so the derivation is strictly weaker
than the census generator and hence kills a subset of what G kills — it is not
an appeal to G's output.  The enumerated space is Algorithm G's own box, not a
narrower one.  My independent check (`checks/tier_check.py`) confirms
algebraically, over the whole box, that `N_lo <= n45 <= N_hi` is *exactly*
"(Lemma 4.10 budget) and (Lemma 4.9 cap)" with 0 mismatches: Tier 1 is not a
new hypothesis, it is those two lemmas with n45 eliminated.

**The Pareto ledger is genuinely required, and now appears inside the proof.**
My earlier observation stands verbatim: the ledger-free system (identities +
TC2c + run caps) admits a_3 = 1 records at (20,0,0) e = 2 and e = 4.  Those are
*precisely* the two censuses that survive Tier 1 in the a_3 clause — Tier 1
kills 148 of 150 and leaves exactly (20,0,0) e=2 (a_3=1, c_1=0) and (20,0,0)
e=4 (a_3=1, c_1=2), each in both b_q1 forms.  So the observation is no longer a
caveat about a limitation; it is the statement of which four table rows carry
the a_3 clause, and each is a single certified frontier value:

    (20,0,0) e=2 b_q1=0: 27 > F(2,16,1,1) = 26
    (20,0,0) e=2 b_q1=1: 26 > F(1,14,1,0) = 19
    (20,0,0) e=4 b_q1=0: 25 > F(2,14,1,1) = 24
    (20,0,0) e=4 b_q1=1: 24 > F(1,12,1,0) = 17

**Independent verification performed here** (`checks/tier_check.py`, all PASS):
the Tier-1 equivalence above (0 mismatches over the whole box); the tallies
140 + 10 = 150 and 148 + 2 = 150 with **0 survivors**, recomputed with this
workdir's own `F`; robustness — rerunning both clauses with the one
un-re-derived table value g(20) = 25 replaced by the strictly weaker C6-B
bound still gives 0 survivors, so no conclusion depends on it; and
discrimination — the identical two tiers *admit* c_2 >= 1 outside the
length-871 budget (1, 2, 1, 1 surviving censuses at (25,0,0) e = 3, 5, 8, 11
and 6 at (30,0,0) e = 5, and 0 at e = 12, matching the published e = 3..11
range), so the exclusion is a consequence of the 871 budget and not a
structural prohibition.

**Honest scope note.**  "Hand proof" here means a *finite case analysis with
printed, independently checkable arithmetic*: 300 censuses, of which 288 die on
a single integer inequality needing no table, and 12 on a single entry of the
capacity table of Appendix B — a table now certified by four independent
complete enumerations.  This is the same standard as the paper's existing
Lemma 5.8 (which turns on F(2,8,0,0) = 20) and THEOREM K2 (F(2,15,2,0) = 25).
It is not a two-line argument, and a reader who wants to check all 300 rows
must read a table; but every row is one inequality between integers, the tables
are printed, and nothing is read off an unprinted enumeration.

**Verdict: the Coverage Theorem is PROVED, with no residual audited-output
step.**  What remains machine-borne is exactly the computer-assisted core the
result is entitled to: the 1111 exhaustive searches themselves (step (g)) and
the set-equality between the derived instance list and the committed run log
(step (f)) — neither of which is a mathematical claim quantified over
orderings.

## 7. THE PRINTED DATA

### 7.1 One command

    python3 approaches/n6coverage/checks/print_census.py > logs/census_table.txt

Output `logs/census_table.txt`: **910 lines, 53,763 bytes (52.5 KB), 4,958
bytes gzipped**.  Small enough for a paper appendix in full, and trivially
small as supplementary data.  Structure:

* **Part A** — the 200 configurations, grouped by structural class, one line
  each: `a2 a3 c1 c2 bq1 | a1 n45 n4 nS | sumc1 sumc2 | LAM U`.
* **Part B** — the 631 instances, grouped by class, one line each:
  `n5 n4 S=(n3x3,n2x2,n1x1) c1 s2=[...] bq1` plus the mode tag `m0` or
  `m0+m1`, followed by the per-class run counts.

The script asserts 200 / 631 / 631+480 = 1111 at the end, so a corrupted run
fails loudly.

Per-class counts (Part A / Part B / loop-exposed):

| class | configs | instances | m1 runs |
|---|---|---|---|
| (20,0,0) e=1..9 | 16,17,33,17,11,23,4,2,4 = 127 | 60,51,70,48,29,43,8,3,8 = 320 | 256 |
| (15,1,0) e=1,2,3,4,7 | 22,16,11,16,4 = 69 | 42,27,17,25,5 = 116 | 34 |
| (10,2,0) e=2 | 4 | 5 | 0 |
| (15,0,1) zh / zp3 | 2 wirings | 95 + 95 = 190 | 190 |
| **total** | **200** | **631** | **480** |

### 7.2 Independence of the regeneration

`checks/census_gen.py` is written from the specification of sect. 3, not from
the artifact's code, and it enumerates a *different* space: the artifact's
`tight_enum.py` enumerates the collapsed tuple (a_2,a_3,c_1,c_2,b_q1,n45,n4)
and tests the short-length multiset only through the interval window G9, while
this implementation enumerates the *full* length multiset (n5, n4, and the
exact (n3,n2,n1)) and projects.  `checks/verify_census.py` checks:

* configuration sets agree class by class, both directions, 0 only-mine /
  0 only-artifact, total 200 = 200;
* instance sets agree class by class against the artifact's `mkjobs.jobs_for`
  **and** against the job function of the reviewer's sweep driver, 0 missing /
  0 extra, total 631;
* `checks/match_runs.py` then matches the derived run list against the
  committed 1111-run log by tag: **identical sets, 0 missing, 0 extra**,
  631 mode-0 + 480 mode-1, 0 SAT, 0 CAPPED, 0 TIMEOUT.

This closes the bridge the referee named: the 631 instances are not "what the
generator happened to produce"; they are the image of a specified algorithm
whose every rejection is proved necessary, re-derived here by a second
enumeration over a different space, and matched run-for-run against the log.

## 8. CONTROLS AND DISCRIMINATION

All in `checks/controls.py`, output `logs/controls.log`.  Object structures are
extracted from the raw strings by `reviews/R-n6-7-workdir/myanalyze.py`, a
third-party analyzer written from raw definitions.

### 8.1 ADMISSION — the machinery admits every real object at its own length

| object | L | (D,X4,Z) e X4h | configuration key | admitted? |
|---|---|---|---|---|
| verified 872 | 872 | (25,0,0) e=25 X4h=0 | (0,0,25,0,0,4,0,100,0) | YES — and it is the class's ONLY configuration |
| verified 873 baseline | 873 | (0,6,0) e=0 X4h=5 | (0,0,0,0,0,24,0,0,0) | YES — and the system FORCES X4h >= 5, the real value |
| m2obj_620_0 | 878 | (55,0,0) e=29 | a_2 = 4 | YES (284 configs in its class) |
| m2obj_620_1 | 877 | (50,0,0) e=29 | a_2 = 3 | YES (138) |
| m2obj_620_11 | 880 | (65,0,0) e=30 | a_2 = 5 | YES (612) |
| m2obj_620_14 | 878 | (55,0,0) e=29 | a_2 = 4 | YES (284) |
| m2obj_620_19 | 878 | (55,0,0) e=29 | a_2 = 4 | YES (284) |
| m2obj_620_23 | 877 | (50,0,0) e=27 | a_2 = 1 | YES (308) |

The six counterexample objects are exactly the R1/R1'-refuting objects of
R-n6-7; they are the only known real superpermutations carrying two-block path
components, so they are the decisive admission control for everything in
sects. 4 and 5 that concerns spans.

### 8.2 ADMISSION of the two-loop inequality (*) on real objects

The proved inequality 5(a_2 + 2a_3 + c_2) <= D − e − Delta_1 is evaluated on
each real object with its own D, e, Delta_1:

| object | a_2 | 5*Lambda | D − e − Delta_1 | bound permits U up to |
|---|---|---|---|---|
| 872 | 0 | 0 | 25 − 25 − 0 = 0 | 0 |
| 873 | 0 | 0 | 0 − 0 − 0 = 0 | 0 |
| m2obj_620_23 (L=877) | 1 | 5 | 50 − 27 − 17 = 6 | 1 (TIGHT) |
| m2obj_620_1 (L=877) | 3 | 15 | 50 − 29 − 3 = 18 | 3 (TIGHT) |
| m2obj_620_0/14/19 (L=878) | 4 | 20 | 55 − 29 − 2 = 24 | 4 (TIGHT) |
| m2obj_620_11 (L=880) | 5 | 25 | 65 − 30 − 5 = 30 | 6 |

This is the decisive control on the two-loop bound.  The inequality is **not**
a bound that always says "2": on real objects at L = 877..880 it permits — and
those objects realise — U = 3, 4 and 5, in four cases exactly at the bound.  It
says 2 at L = 871 because the length-871 budget D = 20/15/10 is small, which is
precisely the mechanism the manuscript claims and could not previously show.

### 8.3 DISCRIMINATION — the machinery does not accept everything

*Ablation over the fifteen Z = 0 classes* (configurations surviving):

| system | configurations |
|---|---|
| full (G1–G11) | **200** |
| TC2c cycle closure OFF | 274 (+74) |
| run caps C6-A OFF | 701 (+501) |
| value ledger OFF | 200 (no change) |
| Pareto ledger OFF | 404 (+204) |
| all four OFF (identities only) | 6513 (+6313) |

* The identities alone admit **6513** configurations; the proved tests reject
  96.9% of them.  The machinery is very far from accepting everything.
* The TC2c-off count **274 reproduces the artifact's own published pre-TC2c
  census exactly** (proof_tight.md §7: 16/32/44/35/22/29/6/3/7 + 22/19/12/19/4
  + 0/4 = 274) — an independent regression on a number the artifact printed
  before the closure lemma was added.
* Every full-system configuration survives with all tests off: the tests are
  monotone filters, as an over-approximating enumeration requires.
* **HONEST FINDING:** the value ledger (G10) is *verdict-neutral at L = 871* —
  removing it revives zero configurations.  This reproduces the artifact's own
  ablation (`n6tight/checks/probe_kill.py`: "relaxing the VALUE ledger alone
  revives 0") and means no published number depends on it.  Its necessity proof
  (Lemma 4.11, coarse form) is therefore not load-bearing.

*Cells the machinery kills outright* (each a proved-necessary consequence, each
a place where an over-permissive census would have shown up):

| class | configs | meaning |
|---|---|---|
| (10,2,0) e=2 X4h=1 | 0 | reproduces THEOREM K1, the quarter-kill |
| (10,2,0) e=2 X4h=2 | 4 | survives, as registered |
| (0,6,0) e=0 X4h=2,3,4 | 0,0,0 | the 873 corner is FORCED to X4h >= 5 |
| (0,6,0) e=0 X4h=5,6 | 1,1 | the real 873's value survives |
| (25,0,0) e=25 | 1 | the 872 corner admits EXACTLY ONE configuration — the real 872's |

*The sharpest discrimination — same code, opposite verdicts on a_2 = 3:*

| question | verdict |
|---|---|
| max a_2 over all fifteen L=871 classes | **2** — a_2 = 3 is REJECTED |
| max a_2 at (50,0,0) e=29 (class of m2obj_620_1, L=877) | 4 — a_2 = 3 ACCEPTED, and the real object has 3 |
| max a_2 at (65,0,0) e=30 (class of m2obj_620_11, L=880) | 7 — a_2 = 5 ACCEPTED, and the real object has 5 |

The identical rejection tests accept three, four and five spans where real
objects have them, and refuse three at length 871.  A census that under-covered
by an accidental over-rejection of spans would fail this control.

## 9. HONEST NEGATIVES, LIMITS, AND WHAT THE MANUSCRIPT MUST CHANGE

### 9.1 Limits of this document

1. *(CLOSED 2026-09-03.)*  `a_3 = 0` and `c_2 = 0` were recorded here as
   audited outputs.  T-n6-fin's two-tier derivation, verified independently in
   `checks/tier_check.py`, turns them into a finite case analysis (sect. 6.4).
   No audited-output step remains in the chain.
2. This document does **not** re-run the 1111 searches (compute budget ~30
   CPU-min; the sweep is ~2.1e11 nodes / ~7 CPU-hours).  It matches the run
   *list* to the committed log tag-for-tag and reads the verdicts from it.
   The verdicts themselves rest on R-n6-7's engine plus the artifact's four
   engines plus R-n6-9's counter-review, with node-for-node agreement in linear
   mode on all 631 jobs.
3. The geometric model M's faithfulness (step (d)) is cited from R-n6-7 §2.1,
   not re-derived here; that step was already the subject of a clause-by-clause
   machine check on the verified 872.  The parts of it that the census controls
   — piece kinds and counts — are re-derived here.
4. THEOREM K2's wiring completeness (the defect class) is a hand argument in
   proof_tight.md §7 plus `z1_corner.py`; this document uses it as given.  It is
   the only class whose configuration set is not produced by Algorithm G.
5. The value ledger's necessity proof (Lemma 4.11, coarse form) is the least
   detailed in sect. 4.  It is also verdict-neutral at L = 871 (sect. 8.3), so
   nothing rests on it.  If a future reviewer disputes it, delete G10: the
   census is unchanged.

### 9.2 Required corrections to `report/PAPER-n6-872.tex`

1. **Lemma 6.8 (`lem:closure`).**  Replace
   "and in every configuration of the census at most two such arcs exist"
   by the proved bound of sect. 5.2 of this document, with its two-step proof
   (deficiency accounting + run cap).  The lemma then contains no appeal to the
   census.  Recommended replacement text for the last sentence of the proof
   sketch: *"The number of such arcs is a_2 + 2a_3, and the deficiency identity
   D = sum(5 − l) together with the component caps gives
   5(a_2 + 2a_3 + c_2) <= D − e; at (10,2,0) and (15,1,0) and at (20,0,0) with
   e >= 6 this is already <= 2, and the residual cases (20,0,0), e in {3,4,5}
   with a_2 + 2a_3 = 3 are refuted by the run caps of Lemma 3.4(1) (Lemma
   5.2 of coverage.md)."*
2. **§6.3 (`sec:search`), "Census".**  The sentence "a finite enumeration lists
   every admissible configuration" must be replaced by, or cross-referenced to,
   the full algorithm specification (sect. 3 above), and the paper must state
   that every rejection test is proved necessary (sect. 4) — currently the
   claim is made only for the *model*, not for the *census*.
2b. Appendix A.6's paragraph "Instance generation (the census)" should carry
   the same eleven-line specification; at present it is prose.
3. **Print the data.**  Ship `logs/census_table.txt` (52.5 KB / 5.0 KB gzipped)
   as an appendix or as supplementary data with the one-line regeneration
   command.  Without it the bridge is not auditable, which was the objection.
4. **Lemma 6.7 (`lem:c2z`).**  Replace "Proof summary: Finite verification"
   by the two-tier derivation of sect. 6.4 — the closed-form pinch
   `N_lo > N_hi` (140 of 150 censuses for c_2, 148 of 150 for a_3, one integer
   inequality each) plus one certified frontier value for each of the
   remaining 12 — and print both Tier-2 tables (11 + 4 rows; they fit in half a
   page).  The lemma must also state that it is load-bearing for the engine's
   *piece set* (no three-block piece), not only for the endgame; the current
   text does not say this.  Recommended status sentence, verbatim, in sect. 9.4
   below.
5. **§6.3, "the census and the instance list were re-derived independently
   twice".**  This is now three times, and the third (this document) is the
   first to re-derive the *configuration* layer over a different enumeration
   space — R-n6-7's `myjobs.py` imports `enumerate_cell` and therefore
   re-derived only the expansion.  The paper should not claim independence at
   the configuration layer on the strength of R-n6-7 alone.

### 9.3 Files

    approaches/n6coverage/
      coverage.md              this document
      STATUS.md, NOTES.md
      MANIFEST.sha256          sha256 of every check and log
      checks/pareto.py         certified chain-capacity F, from the lemma statement
      checks/census_gen.py     ALGORITHMS G and E (independent implementation)
      checks/verify_census.py  G vs tight_enum, E vs mkjobs and the sweep driver
      checks/loopbound.py      the two-loop bound audited under a weakened system
      checks/controls.py       admission + discrimination controls
      checks/match_runs.py     631 instances -> the 1111 committed runs
      checks/tier_check.py     independent verification of T-n6-fin's c2=0/a3=0
                               two-tier derivation, with this workdir's own F
      checks/print_census.py   the printed table
      logs/census_table.txt    200 configurations + 631 instances (52.5 KB)
      logs/verify_census.log logs/loopbound.log logs/controls.log
      logs/match_runs.log logs/tier_check.log

    Regenerate everything (about 8 seconds):
      for f in verify_census loopbound controls match_runs tier_check; do
        python3 approaches/n6coverage/checks/$f.py > approaches/n6coverage/logs/$f.log
      done
      python3 approaches/n6coverage/checks/print_census.py \
        > approaches/n6coverage/logs/census_table.txt

### 9.4 The status sentence the paper should use

For Lemma 6.7 (`lem:c2z`), replacing the present "Proof summary: Finite
verification.":

> *Proof.*  The census coordinate (a_2,a_3,c_1,c_2) of any candidate lies in
> the enumeration box of Algorithm 6's instance generator, which contains 150
> censuses with c_2 >= 1 and 150 with a_3 >= 1.  Eliminating n45 between the
> class budget and the run caps of Lemma 3.4(1) gives
> n45 >= ceil((120 − 3a_1 − 4a_2 − 3a_3 − 4c_1 − 3c_2)/2) and
> n45 <= floor(4(a_1 + LAM)/5); the two are incompatible in 140 of the first
> group and 148 of the second, one integer inequality each.  For the remaining
> 10 + 2 censuses the capacity test of Lemma 3.4(3) is already decided at
> census level, since blocks_rest, LAM and cost_rest do not depend on n45 or
> n4; each dies on one entry of Table B (tables printed in the supplementary
> data, 11 + 4 rows).  Hence c_2 = 0 and a_3 = 0 in every configuration, and
> every cycle in every one of the 631 search instances is type-I.  The
> derivation uses no test beyond those proved necessary for real orderings and
> is unchanged if the single table value g(20) = 25 is replaced by the weaker
> C6-B bound; the same tests admit type-II cycles at type (25,0,0), e = 3..11,
> so the exclusion is a consequence of the length-871 budget, not a structural
> prohibition.

And for the Coverage Theorem as a whole, if the paper states one:

> Every step from "a length-871 superpermutation exists" to "one of the 1111
> committed searches accepts its placement" is closed by a lemma proved from
> the raw definitions; the census generator's every rejection test is proved
> necessary for real orderings, its output is printed in full, and the derived
> instance list is set-identical to the committed run log.  No step of the
> reduction is carried by an unprinted enumeration.
