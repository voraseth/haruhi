# finlem.md — complete derivations for PAPER-n6-872 Lemmas 5.8, 5.9 and 6.7

**Agent T-n6-fin.  Referee objection addressed: the three lemmas were asserted
as "finite feasibility eliminations … reproduced independently" with no
enumeration, no case table and no algorithm specification.  This document
supplies, for each of the three, (a) a complete derivation, (b) a proof that
the enumerated candidate space is a superset of what real length-871 orderings
can produce, (c) a printed case table, and (d) controls.**

## VERDICT (read this first)

| lemma | status |
|---|---|
| **5.8** (no cost-≥5 transition) | **COMPLETE.**  Algorithm A + completeness proof (sect. 1) + a case table that collapses to **five censuses, of which three die by a one-line deficiency count and one by a one-line packing bound; a single candidate reaches the frontier and fails it by margin 4.**  Hand-checkable end to end. |
| **5.9** (the defect-one class) | **COMPLETE.**  A hand proof: three of the five Z-pools die on a single frontier value; for the other two the wiring list is generated **mechanically** from the in/out-edge census of the two non-critical runs (not asserted by hand), and every wiring including six refinements never previously tested is decided by one frontier value.  Exactly two survive. |
| **6.7** (no type-II cycle) | **COMPLETE.**  The elimination reduces to a **closed-form inequality `N_lo > N_hi`** that kills 140 of the 150 relevant censuses by one line of arithmetic each; the remaining 10 die on one certified frontier value each.  The same two tiers also give the companion clause `a3 = 0`.  Controls and the discrimination result reproduce. |

No rejection test used below is unproved.  Nothing here rests on a bound whose
necessity I could not derive; in particular sect. 1.3 proves each of the seven
tests of Algorithm A necessary for **every** first-occurrence ordering in the
cell, and sect. 4.5 re-runs everything with the one unre-derived table value
(`g(20)=25`) removed, with identical verdicts.

Scripts: `checks/frontier.py`, `checks/census.py`, `checks/diffcheck.py`,
`checks/lem58_k1.py`, `checks/lem59_z1.py`, `checks/lem67_c2.py`,
`checks/chainpareto.c`.
Logs: `logs/frontier_c15.log`, `logs/frontier_c16.log`, `logs/diffcheck.log`,
`logs/lem58_k1.log`, `logs/lem58_full_table.log`, `logs/lem59_z1.log`,
`logs/lem67_c2.log`, `logs/lem67_full_table.log`.

---

## 0. Standing setting, notation, and the imported stock

Throughout, "ordering" means the first-occurrence ordering `q_1,…,q_720` of a
superpermutation on `[6]`, with costs `d_k = d(q_k,q_{k+1})`, in the notation of
PAPER-n6-872 §2.  All of the following are **theorems about every ordering**,
with no length hypothesis, and are quoted, not reproved:

| tag | statement | source |
|---|---|---|
| ID | `P = 24 + D/5`, `h = 23 + D/5 + Z − e`, `W = 142 + D/5 + X4 + Z` | Lemma 5.3 (`PNUM/UNIT/THMM-n6`) |
| LED | `Z = zq+zh+zp3+zp2s+zp2g`, `zq ∈ {0,1}` | `LEDGER-n6` |
| T1 | `cnl = e − zL`, `zL = zq+zh+zp2s+zp2g` | `T1-n6` |
| T2 | `pshits = e − Q2 − zp3 − zp2g` | `T2-n6` |
| E1 | `SH ≥ pshits`: every ps-hit heads a **distinct** chain whose **first** path is **short** | `E1-n6` |
| E2 | `ST ≥ cnl`: every CNL ends a **distinct** chain whose **last** path is **short** | `E2-n6` |
| L2 | every pointer edge advances the run start by `ρ`; `ρ` has order exactly 5 | Lemma 6.5 proof |
| C6-A | a chain all of whose paths have length in `{4,5}` has ≤ 4 paths, ≤ 2 of length 4, and no interior length-4 path | `C6-A`, `chain6 A` |
| C6-B | for every chain, `blocks − 2·cost ≤ 4 − 2a − 2b` | `C6-B`, `chain6 B` |
| C6-C | `g(c,a,b)` = max blocks of a chain of cost ≤ c and endpoint type `(a,b)`, table for `c ≤ 16` | `C6-C`; **re-certified in this workdir**, sect. 0.2 |
| I5 | at `slack = 0`, `Q2 = zp2s` | `LEMMAS-n6` |

and, at `Z = 0` and `Q2 = 0`, the rigid-structure lemmas of PAPER §6.1
(= `TC1–TC4` of `n6tight/proof_tight.md`, reviewed sound by R-n6-6):

* **TC1** `NCh = e + 1 + X4h`, with the exact endpoint ledger (chain heads =
  the `e` ps-hit-entered paths + `q_1`'s path + the `X4h` cost-≥4-entered
  paths; dually for enders).
* **TC2** every pointer component alternates blocks of critical runs (one
  block = one link-path) with **single** non-critical runs; a path component
  with `m` blocks has `m−1` nc-runs, a cycle with `m` blocks has `m`.
* **TC2c** every cycle has exactly 5 vertices (L2), so a 1-block cycle carries
  a length-4 path and a 2-block cycle two paths of total length 3.
* **TC3** position ≥ 2 of a component heads its chain; position ≤ m−1 ends its
  chain; hence every cycle path, every interior path of a 3-block component,
  and `q_1`'s path when `q_1`'s component is multi-block, is a **forced
  singleton chain**.
* **TC4** `{4,5}`-paths live only in 1-block path components or in a 1-block
  cycle; with `nS`, `n45`, `n4` counting 1-block path components of length
  ≤ 3, in `{4,5}`, `= 4`, and `LAM` the number of non-forced-singleton chains,
  the maximal `{4,5}`-runs number `R ≤ nS + LAM`, `n45 ≤ 4R`, `n4 ≤ 2R`.

### 0.1 Two facts that are re-proved here because the derivations use them

**(0.1.a) The link relation is acyclic**, so links decompose the 120 classes
into link-*paths* and never into link-cycles.  *Proof.*  A link from `B` to `C`
is a cost-2 exit from `y_B` (the temporally last element of `B`) landing on
`crit(C)`, which therefore occurs immediately after `y_B`.  Since `crit(B)`
starts a run of `B` and `y_B` is `B`'s last element, `time(crit(B)) ≤
time(y_B) < time(crit(C))`.  Around a link-cycle this gives
`time(crit(C)) < time(crit(C))`. ∎

**(0.1.b) Every pointer cycle contains a non-critical run.**  *Proof.*  A
pointer edge is a link, a CNL, a ps-hit, or a premature-sig exit landing on a
non-critical permutation.  A cycle of link edges only is excluded by (0.1.a).
A CNL lands on a non-critical run; a ps-hit is emitted from a premature run end
`z`, and its edge tail is the run starting at `rot(z)`, which is a
non-critical run start.  So any cycle containing a non-link edge meets an
nc-run. ∎  (Used in sect. 3 to conclude `Ncyc = 0` from the wiring list.)

### 0.2 The capacity table, re-certified in this workdir

`checks/chainpareto.c` is a complete depth-first enumeration of the chain
abstraction (pairwise class-disjoint `ρ`-segments joined by exact-distance-3
hops, first head `123456` WLOG by transitivity of relabelling), with **no
pruning other than the cost budget and the class-disjointness that define the
abstraction**, so completeness holds by construction.  Recompiled and re-run
here:

```
logs/frontier_c15.log    nodes =   740,052,451   rows 0..15    (9 s)
logs/frontier_c16.log    nodes = 2,034,132,013   rows 0..16   (23 s)
```

| cost | free | short-first | short-last | both short |
|---|---|---|---|---|
| 0 | 4 | – | – | – |
| 1 | 4 | 4 | 4 | 1 |
| 2 | 7 | 4 | 4 | 4 |
| 3 | 7 | 7 | 7 | 4 |
| 4 | 10 | 7 | 7 | 7 |
| 5 | 10 | 10 | 10 | 7 |
| 6 | 11 | 10 | 10 | 10 |
| 7 | 13 | 11 | 11 | 10 |
| 8 | 14 | 13 | 13 | 11 |
| 9 | 15 | 14 | 14 | 13 |
| 10 | 16 | 15 | 15 | 14 |
| 11 | 17 | 16 | 16 | 15 |
| 12 | 19 | 17 | 17 | 16 |
| 13 | 19 | 19 | 19 | 17 |
| 14 | 22 | 19 | 19 | 19 |
| 15 | 22 | 22 | 22 | 19 |
| 16 | 22 | 22 | 22 | 22 |

The even rows agree entry for entry with the registered `C6-C` table of
`proof6.md` §7, and the whole table agrees with the T-n6-tight
re-certification; this is now a **fourth** independent enumeration of the
frontier.  All 12 typed values used by Lemma 5.9 were also confirmed by
reviewer R-n6-6's own from-scratch table (R-n6-6 §1.5).

**Multi-chain packing.**  For `k ≥ 0` chains of total cost ≤ `m`, of which at
least `sh` have a short first path and at least `st` a short last path,

```
F(k,m,sh,st) = max over c,a,b of  cap(c,a,b) + F(k−1, m−c, max(0,sh−a), max(0,st−b)),
F(0,m,sh,st) = 0 if m ≥ 0 and sh ≤ 0 and st ≤ 0, else −∞,
```

with `cap(c,a,b) = g(c,a,b)` for `c ≤ 16`, `cap = min(25, 4−2a−2b+2c)` for
`17 ≤ c ≤ 20` (registered `g(20)=25` plus monotonicity of `g`, intersected with
C6-B), and `cap = 4−2a−2b+2c` (C6-B alone) beyond.  `F` is non-decreasing in
`k` and in `m` and non-increasing in `sh`, `st`, directly from the recursion.

**Necessity of the `F`-test.**  If a set of `k` chains carries `B` paths in
total, has total cost `≤ m`, and at least `sh` (resp. `st`) of the chains have
a short first (resp. last) path, then `B ≤ F(k,m,sh,st)`: the real chains are
one of the tuples `(c_i,a_i,b_i)` maximised over, and `blocks_i ≤ cap(c_i,a_i,b_i)`
by C6-C/C6-B. ∎

---

## 1. ALGORITHM A — the configuration census, specified and proved complete

Algorithm A is the finite enumeration shared by Lemmas 5.8 and 6.7.  It is
implemented in `checks/census.py` and is a documented restatement of
`n6tight/checks/tight_enum.py::enumerate_cell`; `checks/diffcheck.py` certifies
that the two produce **identical survivor sets** on all 16 habitat cells and
all 6 control cells, and that their `F` values agree over the whole consumed
range (`logs/diffcheck.log`: PASS).

### 1.1 Input, output, enumeration ranges

**Input.** A structural class: a type `(D, X4, Z=0)`, the extra-run count `e`,
and `X4h`.  Derived: `P = 24 + D/5` (ID), `NCh = e + 1 + X4h` (TC1).

**Output.** The set of *configurations* `x = (a2,a3,c1,c2,b_q1,n45,n4)` that
pass all seven tests, where

* `a_m` = number of pointer path components with `m` link-paths (`m = 1,2,3`),
* `c_m` = number of pointer cycles with `m` link-paths (`m = 1,2`),
* `b_q1 = 1` iff `q_1`'s component has ≥ 2 link-paths,
* `n45` = number of 1-block path components whose path has length 4 or 5,
* `n4` = number of those whose path has length exactly 4.

**Enumeration ranges.**  `a2 ∈ [0,e]`, `a3 ∈ [0,⌊(e−a2)/2⌋]`,
`c2 ∈ [0,⌊(e−a2−2a3)/2⌋]`, then `c1 = e − a2 − 2a3 − 2c2` and
`a1 = P − e − a2 − a3` are determined; `b_q1 ∈ {0,1}` (only `{0}` when
`a2+a3 = 0`); `n45 ∈ [0,a1]`, `n4 ∈ [0,n45]`.

**Range completeness.**  By TC2 every component is a path component with
`m ≤ 3` blocks or a cycle with `m ≤ 2` blocks (a cycle has 5 vertices, at least
one of which is an nc-run, so at most 2 blocks; a path component has ≤ 5
vertices, so `Σℓ + m − 1 ≤ 5` with `ℓ ≥ 1` forces `m ≤ 3`).  Counting nc-runs
and link-paths gives the two exact identities

```
(N1)  a2 + 2a3 + c1 + 2c2 = e            (each component's nc-count)
(N2)  a1 + 2a2 + 3a3 + c1 + 2c2 = P      (each component's block count)
```

so `a1 = P − e − a2 − a3`, and every non-negative solution of (N1) lies in the
scanned box.  If `a2 + a3 = 0` then every path component is 1-block, so
`q_1`'s component is 1-block and `b_q1 = 0` — the omission of `b_q1 = 1` there
is therefore not a restriction.  By TC4 a path of length 4 or 5 lies only in a
1-block path component or in a 1-block cycle; the latter has length exactly 4
and is counted by `c1`, so `n45 ≤ a1` and `n4 ≤ n45` exhaust the possibilities.
Hence **every length-871 ordering in the class induces a configuration inside
the scanned box.** ∎

### 1.2 Derived quantities (exact identities or one-sided bounds)

The forced singleton chains of TC3 are the `c1 + 2c2` cycle paths, the `a3`
interior paths of 3-block components, and `q_1`'s path when `b_q1 = 1`; these
are pairwise distinct chains.  Hence, writing "rest" for the chains that are
not forced singletons:

```
#forced singletons = c1 + 2c2 + a3 + b_q1
lam         = NCh − #forced singletons = a2 + a3 + 1 + X4h − b_q1        (exact)
blocks_rest = P   − #forced singletons = a1 + 2a2 + 2a3 − b_q1           (exact)
sh_rest     = a2 + a3                            (lower bound, see 1.3-T7)
st_rest     = a2 + a3 − b_q1                     (lower bound, see 1.3-T7)
nS          = a1 − n45                                                   (exact)
cost_sing   = c1 + 7c2 + 4a3 + 2b_q1             (lower bound on their cost)
cost_rest   = D − cost_sing                      (upper bound on the rest cost)
v_sing      = −c1 − 12c2 − 7a3 − 3b_q1           (upper bound on their value)
V           = P − 2D = Σ_chains (blocks − 2·cost)                        (exact)
```

*Justification of the four one-sided entries.*  A singleton chain consisting of
one path of length `ℓ` has `1` block, cost `5−ℓ` and value `1 − 2(5−ℓ) = 2ℓ−9`.
A 1-block cycle path has `ℓ = 4` exactly (TC2c): cost `1`, value `−1` — hence
`c1` and `−c1`.  A 2-block cycle has two paths of total length 3 (TC2c): cost
`10−3 = 7`, value `2·3 − 18 = −12` — hence `7c2` and `−12c2`.  An interior path
of a 3-block component has `ℓ = 1` exactly (three paths of total length ≤ 3,
each ≥ 1): cost 4, value −7.  `q_1`'s path in a multi-block component has
`ℓ ≤ 3` (TC2 caps), so cost ≥ 2 and value ≤ −3.  Using the *minimum* cost makes
`cost_rest` an **upper** bound on the true rest cost, and using the *maximum*
value makes `v_sing` an **upper** bound; both are the conservative direction. ∎

### 1.3 The seven rejection tests, each proved necessary

Fix a length-871 ordering in the class and let `x` be its configuration.

**T0 (`nonneg`).**  `c1 ≥ 0`, `a1 ≥ 0`.  Counts.

**T1–T3 (`C6A_n45`, `C6A_n4`, `C6A_R`).**  Let `R` be the number of maximal
runs of consecutive `{4,5}`-length paths inside the chains.  By TC4,
`R ≤ nS + LAM = nS + lam =: Rmax`, and by C6-A applied to each maximal run
(a contiguous sub-sequence of a chain is a chain), each run holds ≤ 4 paths of
length in `{4,5}` and ≤ 2 of length 4.  Every `{4,5}`-path is in some maximal
run, so `n45 ≤ 4R ≤ 4·Rmax`, `n4 ≤ 2R ≤ 2·Rmax`, and
`R ≥ max(⌈n45/4⌉, ⌈n4/2⌉)`, whence `max(⌈n45/4⌉,⌈n4/2⌉) ≤ Rmax`. ∎

**T4 (`length_budget`).**  The 120 rotation classes are exactly the members of
the link-paths, so the path lengths sum to 120.  Splitting by component type
and using the TC2/TC2c caps (`n45`-components: length `5` or `4`, contributing
`heavy = 4n4 + 5(n45−n4)` exactly; `nS`-components: length in `[1,3]`;
2-block components: total length in `[2,4]`; 3-block components: exactly 3;
1-block cycles: exactly 4; 2-block cycles: exactly 3),

```
rem := 120 − heavy − 3a3 − 4c1 − 3c2   ∈   [ nS + 2a2 ,  3nS + 4a2 ].
```
∎

**T5 (`TC5_value`).**  Sum C6-B over all `NCh` chains.  Chain costs sum to `D`
(each path lies in one chain; the deficiencies sum to `D`), and blocks sum to
`P`, so `V = P − 2D = Σ_i (blocks_i − 2·cost_i)`.  For the forced singletons
the summand is *exactly* `2ℓ−9`, bounded above by `v_sing` (sect. 1.2); for
each rest chain, `blocks_i − 2·cost_i ≤ 4 − 2a_i − 2b_i` by C6-B, and at least
`sh_rest` of them have `a_i = 1` and at least `st_rest` have `b_i = 1`
(T7 below).  Hence `V ≤ v_sing + 4·lam − 2·sh_rest − 2·st_rest`. ∎

**T6 (`TC5_cost_neg`).**  `cost_rest = D − cost_sing ≥ 0` since chain costs are
non-negative and sum to `D`.

**T7 (`TC5_pareto`).**  The rest chains number `lam`, carry `blocks_rest`
paths, and have total cost `≤ cost_rest`.  Their short-endpoint obligations:
by TC3(1) the position-2 path of every 2-block component and the position-3
path of every 3-block component **heads** its chain, and by the TC2 caps those
paths have length ≤ 3, hence are short; none of them is a forced singleton;
they are `a2 + a3` distinct chains — so at least `sh_rest = a2 + a3` rest
chains have a short first path.  Dually by TC3(2) the position-1 path of every
2-block component and the position-1 path of every 3-block component **ends**
its chain and is short; these are `a2 + a3` distinct chains, of which at most
`b_q1` is the forced singleton `q_1`'s path — so at least
`st_rest = a2 + a3 − b_q1` rest chains have a short last path.  By the
necessity of the `F`-test (sect. 0.2), `blocks_rest ≤ F(lam, cost_rest,
sh_rest, st_rest)`. ∎

**Conclusion (completeness of Algorithm A).**  Every length-871 ordering in the
class induces a configuration lying in the scanned box and passing T0–T7.
Therefore *a class whose Algorithm-A output is empty contains no length-871
ordering*, and — the form used by Lemma 6.7 — *no length-871 ordering in the
class has a configuration coordinate outside the Algorithm-A output.* ∎

### 1.4 Fidelity and independence

* `checks/diffcheck.py` — survivor-set equality with `tight_enum.py` on
  16 + 6 cells; `F` agreement on `k ≤ 5, cost ≤ 20, sh,st ≤ 2`; and the
  'lin' cap-mode is certified to over-cover the 'full' mode.  All PASS.
* R-n6-6 §1.4 re-derived the same eliminations from an **independently coded**
  enumeration with exact per-component length counts (`mykill.py`) and its own
  frontier table, reaching the same verdicts.
* The frontier itself is now certified by four independent enumerations
  (sect. 0.2).

---

## 2. LEMMA 5.8 — no transition of cost ≥ 5

> **Lemma 5.8.**  In the class `(10,2,0)`, `e = 2`, the sub-case `X4h = 1` is
> infeasible.  Hence `X4h = X4` in every class of Theorem 5.7, and no
> transition of cost ≥ 5 occurs in any length-871 superpermutation.

### 2.1 The reduction to one cell (hand proof)

`X4 = Σ_{d≥4}(d−3)` and `X4h = #{d ≥ 4}`; each cost-≥4 transition contributes
between `1` and `3` to `X4` because `d ≤ 6`, so `⌈X4/3⌉ ≤ X4h ≤ X4`, and
`X4h = X4` **iff every cost-≥4 transition has `d = 4` exactly**, i.e. iff no
transition of cost ≥ 5 occurs.  Over the sixteen classes of Theorem 5.7:

| type | `X4` | consequence |
|---|---|---|
| `(20,0,0)`, `(15,0,1)` | 0 | `X4h = 0 = X4` trivially |
| `(15,1,0)` | 1 | `1 = ⌈1/3⌉ ≤ X4h ≤ 1`, so `X4h = 1 = X4` |
| `(10,2,0)` | 2 | `X4h ∈ {1,2}`; the case `X4h = 1` is what remains |

So the whole lemma reduces to emptying the single cell
`(D,X4,Z) = (10,2,0)`, `e = 2`, `X4h = 1`.  Its parameters: `P = 26` (ID),
`NCh = e+1+X4h = 4` (TC1), `D = 10`.

### 2.2 The case analysis (`checks/lem58_k1.py`, `logs/lem58_k1.log`)

**Level 1 — the five censuses.**  Solutions of `a2 + 2a3 + c1 + 2c2 = 2`.  Each
non-1-block piece has an *exact* deficiency by TC2/TC2c: a 2-block component
carries two paths of total length ≤ 4, cost ≥ 6; a 3-block component three
paths of length 1, cost 12; a 1-block cycle cost 1; a 2-block cycle cost 7.
Since chain costs sum to `D = 10`:

| `a2 a3 c1 c2` | `a1` | deficiency floor | verdict |
|---|---|---|---|
| 0 0 2 0 | 24 | 2 | → level 2 |
| 0 0 0 1 | 24 | 7 | → level 2 |
| 0 1 0 0 | 23 | **12 > 10** | DEAD, one line |
| 1 0 1 0 | 23 | 7 | → level 2 |
| 2 0 0 0 | 22 | **12 > 10** | DEAD, one line |

**Level 2 — the `(n45,n4)` analysis.**  For each surviving census, the class
budget T4 and the run cap T1–T3 are combined exactly as in sect. 4.1: writing
`N_lo = ⌈(120 − 3a1 − 4a2 − 3a3 − 4c1 − 3c2)/2⌉` and `N_hi = ⌊4(a1+lam)/5⌋`,
a census with `N_lo > N_hi` is empty.

| census | `lam` | `N_lo` | `N_hi` | verdict |
|---|---|---|---|---|
| `(0,0,0,1)` (a type-II cycle) | 2 | 23 | 20 | DEAD |
| `(1,0,1,0)`, `b_q1=0` | 3 | 22 | 20 | DEAD |
| `(1,0,1,0)`, `b_q1=1` | 2 | 22 | 20 | DEAD |
| `(0,0,2,0)` | 2 | 20 | 20 | **survives — one slice, `n45 = 20`** |

For `(0,0,2,0)` the two bounds pinch: `n45 = 20`, and then the length budget
`rem = 120 − heavy − 8 ∈ [nS, 3nS] = [4,12]` with `heavy = 5·20 − n4` forces
`n4 = 0` (`rem = 12`).  So exactly **one** candidate reaches the frontier.

**Level 3 — the deciding candidate.**

```
x = (a2,a3,c1,c2,b_q1,n45,n4) = (0,0,2,0,0,20,0)
a1 = 24,  nS = 4,  lam = 2,  blocks_rest = 24,  cost_sing = 2,  cost_rest = 8
class budget: 120 = 5·20 + (4 short paths, total 12) + 4·2         OK
value ledger: V = P − 2D = 6  ≤  v_sing + 4·lam = −2 + 8 = 6       OK (tight)
frontier:     blocks_rest = 24  >  F(2,8,0,0) = g(4)+g(4) = 20     FAILS by 4
```

`F(2,8,0,0) = 20`: two chains of total cost 8, so `max_c (g(c)+g(8−c)) =
g(4)+g(4) = 10+10 = 20` from the certified table.  **Zero configurations
survive.**

*(This corrects the arithmetic slip flagged by R-n6-6 finding F2: the value
is 20, not the 21 printed in `proof_tight.md`; the inequality only
strengthens.)*

### 2.3 Completeness

By sect. 1.3 every length-871 ordering in the cell induces a configuration
passing T0–T7 inside the scanned box.  The scan produced 2 402 candidates
(full-tuple convention; 1 872 in the slice convention of `tight_enum.py`) and
zero survivors.  Therefore the cell is empty, `X4h = 2 = X4` at `(10,2,0)`, and
by sect. 2.1 no length-871 ordering has a transition of cost ≥ 5. ∎

### 2.4 Ablation (which hypotheses the kill actually uses)

`logs/lem58_k1.log` §E, re-running the enumeration with one test family
disabled (and the disabled candidates carried on to the remaining tests):

```
drop none                  -> 0 configurations revived
drop run cap C6-A          -> 0 configurations revived
drop value ledger C6-B     -> 0 configurations revived
drop Pareto frontier C6-C  -> 1 configuration revived
```

So the **class/length budget together with the frontier kills the cell on its
own**; the run cap and the value ledger are redundant here.  This reproduces
exactly what `n6tight/checks/probe_kill.py` prints and confirms R-n6-6's
finding F1 (`proof_tight.md`'s prose claim that *both* the run cap and the
frontier are needed is wrong — the kill is *more* robust than claimed).  The
paper's sentence should say: *the elimination uses only the exact class-length
budget and the certified frontier.*

### 2.5 Controls

| control | result |
|---|---|
| same cell at `X4h = 2` | **4 configurations survive** — the registered count; the cell is *not* emptied |
| `(25,0,0)`, `e=25` (the verified 872) | 1 configuration survives, and it is **exactly** the real 872's shape (`a1 = 4` length-5 paths, `c1 = 25` type-I cycles) |
| `(0,6,0)`, `e=0`, `X4h=5` (the verified 873s) | survives at the real `X4h`; also at `X4h = 6` |

The `X4h = 2` control is the sharp one: the algorithm distinguishes the two
sub-cases of the same cell, so the emptiness at `X4h = 1` is a consequence of
`X4h`, not of the machinery.

---

## 3. LEMMA 5.9 — the defect-one class `(15,0,1)`, `e = 2`

> **Lemma 5.9.**  In the class `(15,0,1)`, `e = 2`, the single defect unit must
> be a heavy landing on a non-critical permutation (`zh`) or a premature
> cost-3 exit (`zp3`); exactly two component wirings of the pointer graph
> survive, each with its complete skeleton determined; and the ordering has no
> pointer cycles and exactly three chains.

Parameters: `D = 15`, `X4 = X4h = 0`, `Z = 1`, so `P = 27` and `h = 25` (ID).
`slack = 0` gives `Q2 = zp2s` (I5).  Chain costs sum to `D = 15` and the 27
paths are distributed among the `NCh` chains.

### 3.1 The chain count at `Z = 1` (TC1z)

At `X4h = 0` all 25 heavies have `d = 3`.  A `d = 3` heavy fails to be a hop
only by being premature (a `zp3` unit) or by landing on a non-critical
permutation (a `zh` unit); every other heavy leaves a completion at a path end
(its class has no out-link) and lands on a critical permutation that is not
link-entered, hence a path head — a hop.  Since `Z = 1` at most one of `zh`,
`zp3` is 1.  So `#hops = 25 − zh − zp3` and

```
NCh = P − #hops = 27 − (25 − zh − zp3) = 2 + zh + zp3.
```

### 3.2 Stage 1 — the branch table (`logs/lem59_z1.log` §A)

LED puts the unit in exactly one of the five pools.  T1, T2 and I5 give:

| pool | `Q2` | `cnl` | `pshits` | `NCh` | test | verdict |
|---|---|---|---|---|---|---|
| `zq` | 0 | 1 | 2 | 2 | `27 ≤ F(2,15,2,1) = 24` | **DEAD** |
| `zh` | 0 | 1 | 2 | 3 | → stage 2 | |
| `zp3` | 0 | 2 | 1 | 3 | → stage 2 | |
| `zp2s` | 1 | 1 | 1 | 2 | `27 ≤ F(2,15,1,1) = 25` | **DEAD** |
| `zp2g` | 0 | 1 | 1 | 2 | `27 ≤ F(2,15,1,1) = 25` | **DEAD** |

The test is the `F`-necessity of sect. 0.2 applied to *all* chains at once
(`k = NCh = 2`, total cost `D = 15`, with `sh = pshits` short-first chains by
E1 and `st = cnl` short-last chains by E2).  Three branches die.  In
particular `zp2s = 0`, hence `Q2 = zp2s = 0` **on the whole class**.

### 3.3 Stage 2 — the wiring lists, generated mechanically

The two surviving branches have `NCh = 3` and need the component structure.
The list of wirings is *not* asserted; it is generated from the in/out-edge
census of the two non-critical runs, which is forced by the pool:

*Edge census.*  A run start is `q_1` or the landing of exactly one transition
(Prop. 1(c),(f)); that transition contributes a pointer in-edge unless it is a
heavy or an S-exit.  Dually the pointer out-edge of the run starting at `u` is
generated by the exit of `z = rot^{-1}(u)`, which for a non-critical `u` is a
premature run end; it contributes an edge unless it is a heavy or an S-exit.
The `e = 2` non-critical run starts are entered by the transitions landing on
non-critical permutations, i.e. by the `cnl` CNLs plus the `zh` heavy plus
`zq` (`= 0` here); the `e = 2` premature run ends exit as the `pshits`
ps-hits plus the `zp3` heavy plus `Q2` S-exits (`= 0` here).  Hence

| branch | nc run | in-edge | out-edge |
|---|---|---|---|
| `zh` | `ncH` | none (entered by the `zh` heavy) → **source** | ps-hit |
| `zh` | `nc2` | CNL | ps-hit |
| `zp3` | `nc1` | CNL | ps-hit |
| `zp3` | `nc2` | CNL | none (its premature end is the `zp3` heavy) → **sink** |

*Alternation.*  Two nc-runs are never pointer-adjacent (an edge into an nc-run
is a CNL, whose tail is a critical run) and two blocks are never adjacent (an
edge between two critical runs is a link, which would merge the two link-paths
into one).  So each nc-carrying component is a strictly alternating word in
blocks `K` and nc-runs, with an nc-run at an end only if it lacks the
corresponding edge, and a cycle only if every nc-run in it has both edges.
`checks/lem59_z1.py::components` enumerates all such words; it returns
**exactly three shapes per branch**, matching R-n6-6's independent hand
re-derivation:

```
zh :   [ncH K1] + [K2 nc2 K3]      [ncH K1] + cycle[nc2 K2]      [ncH K1 nc2 K2]
zp3:   [K1 nc1 K2] + [K3 nc2]      cycle[nc1 K1] + [K2 nc2]      [K1 nc1 K2 nc2]
```

*Lengths.*  L2 caps every component at 5 vertices and pins a cycle at exactly
5, so a component with `k` blocks and `j` nc-runs has `Σℓ + j ≤ 5` (`= 5` on a
cycle) and each of its blocks has `ℓ ≤ ℓ_max := 5 − j − (k−1)`.

*Chain ledger per wiring.*  A block **heads** its chain iff it is ps-entered,
or is `q_1`'s path, or is the target of the `zp3` heavy; it **ends** its chain
iff it emits a CNL, or emits the `zh` heavy, or is the globally last path.  A
block that does both is a forced singleton chain of cost `≥ 5 − ℓ_max`.  The
ledger `(blocks_rest, lam, cost_rest, sh_rest, st_rest)` is then computed
exactly as in sect. 1.2 (with `sh_rest`/`st_rest` counting only ps-entered
heads and CNL-emitting enders, which E1/E2 certify short), and the wiring
survives iff `blocks_rest ≤ F(lam, cost_rest, sh_rest, st_rest)`.

### 3.4 Refinement monotonicity — why the "generic" wiring suffices

Designating `q_1`'s path, the `zh`-emitting path, the `zp3`-entered path or the
globally last path to be a particular block of an nc-component turns that block
into a forced singleton chain.  This lowers `blocks_rest` and `lam` by 1, and
`cost_rest` by that block's cost floor `c`, and lowers `sh_rest`/`st_rest` by
the block's own endpoint types `a`,`b`.  Since

```
F(k, m, sh, st)  ≥  cap(c,a,b) + F(k−1, m−c, max(0,sh−a), max(0,st−b))
                 ≥  1        + F(k−1, m−c, …)
```

(the first line is one branch of `F`'s own maximum; `cap(c,a,b) ≥ 1` because
the singleton chain exists), a wiring failing `blocks_rest ≤ F(…)` continues
to fail after any such designation.  **Hence a shape whose undesignated
("generic") wiring is already dead is dead in every refinement**, and the
finitely many refinements need only be run on the shapes that survive
generically — which is what pins their skeletons.

### 3.5 The case table (`logs/lem59_z1.log` §B,§C)

Branch `zh = 1` (`P = 27`, `D = 15`, `NCh = 3`):

| wiring | forced singletons | test | verdict |
|---|---|---|---|
| `[ncH K1] + [K2 nc2 K3]`, generic | – | `27 ≤ F(3,15,2,1) = 30` | **ALIVE** |
| … refinement `q_1 = K2` | `K2` (cost ≥ 2) | `26 ≤ F(2,13,2,0) = 23` | DEAD |
| … refinement `zh`-emitter `= K1` | `K1` (cost ≥ 1) | `26 ≤ F(2,14,1,1) = 24` | DEAD |
| … refinement global end `= K1` | `K1` | `26 ≤ F(2,14,1,1) = 24` | DEAD |
| … refinement `zh`-emitter `= K3` | `K3` (cost ≥ 2) | `26 ≤ F(2,13,1,1) = 23` | DEAD |
| … refinement global end `= K3` | `K3` | `26 ≤ F(2,13,1,1) = 23` | DEAD |
| `[ncH K1] + cycle[nc2 K2]`, generic | `K2` (`ℓ = 4`, cost 1) | `26 ≤ F(2,14,1,0) = 25` | DEAD |
| `[ncH K1 nc2 K2]`, generic | `K1` (`ℓ ≤ 2`, cost ≥ 3) | `26 ≤ F(2,12,1,0) = 23` | DEAD |

Branch `zp3 = 1`:

| wiring | forced singletons | test | verdict |
|---|---|---|---|
| `[K1 nc1 K2] + [K3 nc2]`, generic | – | `27 ≤ F(3,15,1,2) = 30` | **ALIVE** |
| … refinement `q_1 = K1` / `zp3`-target `= K1` | `K1` (cost ≥ 2) | `26 ≤ F(2,13,1,1) = 23` | DEAD |
| … refinement `q_1 = K3` / `zp3`-target `= K3` | `K3` (cost ≥ 1) | `26 ≤ F(2,14,1,1) = 24` | DEAD |
| … refinement global end `= K2` | `K2` (cost ≥ 2) | `26 ≤ F(2,13,0,2) = 23` | DEAD |
| `cycle[nc1 K1] + [K2 nc2]`, generic | `K1` (`ℓ = 4`, cost 1) | `26 ≤ F(2,14,0,1) = 25` | DEAD |
| `[K1 nc1 K2 nc2]`, generic | `K2` (`ℓ ≤ 2`, cost ≥ 3) | `26 ≤ F(2,12,0,1) = 23` | DEAD |

All twelve `F`-values independently recomputed by R-n6-6 §1.5
(`F(2,15,2,0)=25`, `F(2,15,1,1)=25`, `F(2,14,1,0)=25`, `F(2,12,1,0)=23`,
`F(3,15,2,1)=30`, `F(2,13,2,0)=23`, `F(2,14,0,1)=25`, `F(1,13,0,0)=19`,
`F(2,12,0,1)=23`, `F(3,15,1,2)=30`, `F(2,13,1,1)=23`, `F(2,14,1,1)=24`) are
reproduced here on this workdir's own re-enumerated table
(`python3 checks/frontier.py` — F SELF-CHECK: PASS).  The `zq` row above uses
the sharper `F(2,15,2,1)=24` (the `ST ≥ cnl` obligation of E2, which
`z1_corner.py` discarded) rather than `F(2,15,2,0)=25`; either kills.  The six
`zh`-emitter / global-end refinements are **new**: they were not tested by
`n6tight/checks/z1_corner.py`, and they all die, which is what upgrades the
paper's "each with its complete skeleton determined" from an assertion to a
verified statement.

### 3.6 Conclusion, and the three extra facts

Exactly **two** wirings survive, both fully generic:

```
zh -branch :  [ncH  K1] + [K2  nc2  K3],   q_1's path an m = 1 component,
              ℓ(K1) ≤ 4,  ℓ(K2) + ℓ(K3) ≤ 4
zp3-branch :  [K1  nc1  K2] + [K3  nc2],   q_1's path an m = 1 component,
              ℓ(K1) + ℓ(K2) ≤ 4,  ℓ(K3) ≤ 4
```

* `Q2 = 0`: from the death of the `zp2s` branch (sect. 3.2) and `Q2 = zp2s`.
* `Ncyc = 0`: by (0.1.b) every pointer cycle contains a non-critical run; every
  wiring in which a non-critical run lies on a cycle (`zh`-shape 2, `zp3`-shape
  2) is dead; so no cycle exists.
* `NCh = 3`: `2 + zh + zp3` with `zh + zp3 = 1`.

which is precisely Lemma 5.9. ∎

### 3.7 Completeness of the enumeration

The branch list is complete by LED (`Z = 1` puts the unit in exactly one of
five pools).  The shape list is complete because (i) each nc-carrying component
is a strictly alternating word (proved above from "no nc–nc edge" and "no
block–block edge"), (ii) the endpoints of such a word are constrained exactly
by the edge census, and (iii) `components()` enumerates every ordered set
partition of the two nc-runs into components together with every path/cycle
choice, rejecting the combinations the edge census forbids.  The designation
list is complete because `q_1`'s path, the `zh` emitter, the `zp3` target and
the global end are each either one of the finitely many blocks of the
nc-components or lie outside them (the "generic" option), and by sect. 3.4 a
generic death implies death for all designations.  Finally each verdict is the
`F`-necessity of sect. 0.2 with parameters that are all one-sided in the safe
direction (`ℓ_max` upper bounds give cost **floors**; `sh_rest`/`st_rest` count
only obligations E1/E2 certify).  So no real length-871 ordering of the class
is rejected. ∎

---

## 4. LEMMA 6.7 — the cycle-shape exclusion (`c2 = 0`)

> **Lemma 6.7.**  In every one of the sixteen classes of Theorem 5.7, every
> component configuration satisfying the proved constraints contains no
> type-II cycle and no three-block path component.  Consequently every cycle in
> every one of the 631 search instances is type-I.

This is the load-bearing one: it is what licenses Algorithm 6 to place only
type-I cycles.  The elimination is Algorithm A of sect. 1 with `c2 ≥ 1` forced;
sect. 1.3 is exactly the required completeness proof.  What follows makes the
elimination *readable*: it collapses to one inequality per census.

### 4.1 The closed-form kill (Tier 1)

Two of Algorithm A's tests do not involve `n4` at all, and combining them
eliminates `n45` as well.

*Lower bound on `n45` from the class budget (test T4).*  The 120 classes are
the members of the link-paths, so, using the exact per-component length data of
sect. 1.3-T4 and `length ≤ 5` for an `n45`-component, `length ≤ 3` for an
`nS`-component, `≤ 4` for a 2-block component:

```
120 ≤ 5·n45 + 3·(a1 − n45) + 4a2 + 3a3 + 4c1 + 3c2
n45 ≥ N_lo := ⌈ (120 − 3a1 − 4a2 − 3a3 − 4c1 − 3c2) / 2 ⌉ .
```

*Upper bound on `n45` from the run cap (tests T1–T3).*  `n45 ≤ 4R` and
`R ≤ nS + lam = a1 − n45 + lam`, so `5·n45 ≤ 4(a1 + lam)`:

```
n45 ≤ N_hi := ⌊ 4(a1 + lam) / 5 ⌋ ,   lam = a2 + a3 + 1 + X4h − b_q1 .
```

Since `b_q1 ∈ {0,1}` only through `−b_q1` in `lam`, taking `b_q1 = 0`
**maximises** `N_hi` and therefore gives the weakest test; the table below is
run at that weakest setting, so a `DEAD` there is a `DEAD` for both `b_q1`.

**A census with `N_lo > N_hi` is empty.**  Over the sixteen classes there are
**150** censuses `(a2,a3,c1,c2)` with `c2 ≥ 1`, and **140 of them die by this
one line**; the full 150-row table is `logs/lem67_c2.log` §A.  Representative
rows:

| class | `a2 a3 c1 c2` | `a1` | `lam` | `N_lo` | `N_hi` | verdict |
|---|---|---|---|---|---|---|
| `(20,0,0)` `e=3` | 1 0 0 1 | 24 | 2 | 21 | 20 | DEAD |
| `(20,0,0)` `e=4` | 0 0 0 2 | 24 | 1 | 21 | 20 | DEAD |
| `(20,0,0)` `e=4` | 0 1 0 1 | 23 | 2 | 23 | 20 | DEAD |
| `(15,1,0)` `e=7` | 5 0 0 1 | 15 | 7 | 26 | 17 | DEAD |
| `(10,2,0)` `e=2` `X4h=1` | 0 0 0 1 | 24 | 2 | 23 | 20 | DEAD |
| `(10,2,0)` `e=2` `X4h=2` | 0 0 0 1 | 24 | 3 | 23 | 21 | DEAD |

*Why it works — the mechanism in one sentence.*  Replacing two type-I cycles
by one type-II cycle removes 5 classes from the cycle cover (8 → 3) and adds 5
to the deficiency bill (2 → 7); the missing 5 classes must be found among the
1-block components as extra length-5 paths, and `N_lo` rises by more than the
run cap `N_hi` allows.

### 4.2 The frontier kill (Tier 2)

Exactly **10** censuses survive Tier 1.  For them `blocks_rest`, `lam`,
`cost_rest`, `sh_rest`, `st_rest` are functions of `(a2,a3,c1,c2,b_q1)` only —
so the frontier test T7 is itself a *census-level* test, and one line each
finishes the job (`logs/lem67_c2.log` §B, complete):

| class | `a2 a3 c1 c2 b_q1` | `blocks_rest` | `lam` | `cost_rest` | `sh st` | `F` | verdict |
|---|---|---|---|---|---|---|---|
| `(20,0,0)` `e=2` | 0 0 0 1 0 | 26 | 1 | 13 | 0 0 | 19 | DEAD |
| `(20,0,0)` `e=3` | 0 0 1 1 0 | 25 | 1 | 12 | 0 0 | 19 | DEAD |
| `(20,0,0)` `e=4` | 0 0 2 1 0 | 24 | 1 | 11 | 0 0 | 17 | DEAD |
| `(20,0,0)` `e=4` | 1 0 1 1 0 | 25 | 2 | 12 | 1 1 | 21 | DEAD |
| `(20,0,0)` `e=4` | 1 0 1 1 1 | 24 | 1 | 10 | 1 0 | 15 | DEAD |
| `(20,0,0)` `e=5` | 0 0 3 1 0 | 23 | 1 | 10 | 0 0 | 16 | DEAD |
| `(20,0,0)` `e=6` | 0 0 4 1 0 | 22 | 1 |  9 | 0 0 | 15 | DEAD |
| `(20,0,0)` `e=7` | 0 0 5 1 0 | 21 | 1 |  8 | 0 0 | 14 | DEAD |
| `(20,0,0)` `e=9` | 0 0 7 1 0 | 19 | 1 |  6 | 0 0 | 11 | DEAD |
| `(15,1,0)` `e=2` | 0 0 0 1 0 | 25 | 2 |  8 | 0 0 | 20 | DEAD |
| `(15,1,0)` `e=4` | 0 0 2 1 0 | 23 | 2 |  6 | 0 0 | 17 | DEAD |

(11 rows: the `(20,0,0)` `e=4` census `1 0 1 1` contributes both `b_q1` values.)
The first row is the paper's worked example: at `(20,0,0)`, `e = 2`, a type-II
cycle spends both non-critical runs, leaving `lam = 1` chain that must carry
`blocks_rest = 26` paths at cost `cost_rest = D − 7·c2 = 13`, against
`F(1,13,0,0) = g(13) = 19`.

**Survivors of Tier 2: 0.**  So `c2 = 0` in every one of the sixteen classes.

### 4.3 The companion clause `a3 = 0`

The identical two tiers, run over the 150 censuses with `a3 ≥ 1` (and `c2`
free), give **148 closed-form kills and 2 frontier kills**
(`logs/lem67_c2.log` §G):

| class | `a2 a3 c1 c2 b_q1` | `N_lo` | `N_hi` | `blocks_rest` | `lam` | `cost_rest` | `F` | verdict |
|---|---|---|---|---|---|---|---|---|
| `(20,0,0)` `e=2` | 0 1 0 0 0 | 21 | 21 | 27 | 2 | 16 | 26 | DEAD |
| `(20,0,0)` `e=2` | 0 1 0 0 1 | 21 | 21 | 26 | 1 | 14 | 19 | DEAD |
| `(20,0,0)` `e=4` | 0 1 2 0 0 | 20 | 20 | 25 | 2 | 14 | 24 | DEAD |
| `(20,0,0)` `e=4` | 0 1 2 0 1 | 20 | 20 | 24 | 1 | 12 | 17 | DEAD |

So no configuration has a three-block path component either — the second half
of Lemma 6.7.

### 4.4 Cross-check at full granularity, and the published tallies

Running Algorithm A candidate by candidate with `c2 ≥ 1` forced
(`logs/lem67_c2.log` §C, per-candidate witnesses in
`logs/lem67_full_table.log`, 54 235 lines):

```
total c2>=1 candidates over the sixteen classes:  54 233   SURVIVORS 0
```

Per-class tallies in the slice convention of `tight_enum.py` reproduce the
published `n6c2probe` numbers exactly, e.g.

```
(20,0,0) e=2 : 258 candidates = 229 length budget + 23 run cap + 6 frontier
```

which is the sentence printed in the paper's proof of Lemma 6.7.  Classes
`(20,0,0) e=1` and `(15,1,0) e=1` contribute **no** `c2 ≥ 1` candidate at all:
a type-II cycle consumes two non-critical runs and `e = 1`.

Finally, running Algorithm A with `c2` and `a3` **free** on the sixteen classes
returns **200** surviving configurations — the registered census count of the
paper — and every one of them has `c2 = 0` and `a3 = 0`.

### 4.5 Robustness: the elimination does not use the one un-re-derived value

The only table entry above cost 16 that Algorithm A consults is the registered
`g(20) = 25`, which this workdir did not re-enumerate.  Re-running everything
in cap-mode `lin`, where `cap(c,a,b) = 4 − 2a − 2b + 2c` (C6-B alone, a
strictly weaker upper bound) for every `c > 16`:

```
c2>=1 survivors over the sixteen classes in mode 'lin':  0
controls still survive in mode 'lin':                     True
```

`checks/diffcheck.py` also certifies that mode `lin` over-covers mode `full` on
all 22 cells.  So **no conclusion in this document depends on `g(20) = 25`.**

### 4.6 Discrimination: the exclusion is a budget consequence

If the constraint system forbade type-II cycles structurally, the elimination
would be worthless.  It does not.  With the *identical* constraint set, `c2 ≥ 1`
configurations **survive** outside the length-871 budget
(`logs/lem67_c2.log` §E):

| cell | `c2 ≥ 1` survivors | an example |
|---|---|---|
| `(25,0,0)` `e=3` | 9 | `(a2,a3,c1,c2,b_q1,n45,n4) = (1,0,0,1,0,19,0)` |
| `(25,0,0)` `e=5` | 11 | `(1,0,2,1,0,18,0)` |
| `(25,0,0)` `e=11` | 1 | `(1,0,8,1,0,15,0)` |
| `(30,0,0)` `e=3` | 97 | `(0,0,1,1,0,16,0)` |

At `(25,0,0)` the admitting range is exactly `e = 3, …, 11`, reproducing the
range quoted in the paper; over `D ∈ {25,30}` thirty `(D,e)` cells admit
`c2 ≥ 1`.  So `c2 = 0` at `D = 20` is forced by the length-871 budget, not by
the machinery.

To the same end at the *engine* level, `n6c2probe/checks/mysweep_c2.c` extends
the endgame of Algorithm 6 with type-II placement (two non-critical slots at
`ρ`-distance 2, covering the orbit's other three classes): it regresses
node-for-node on the committed instances with the extension switched off
(job 1: UNSAT, 303 579 nodes; cycle job 113: UNSAT, 466 304 nodes; 872 census
control SAT in 30 nodes) and finds a *planted* type-II census satisfiable
(SAT, 25 749 nodes).  So neither the census nor the search engine is
structurally blind to type-II cycles.

---

## 5. Controls, at the lengths where real objects live

Nothing certified above may exclude a real superpermutation at its own length.
All controls are asserted inside the scripts (an `assert` failure aborts them).

| control | source | result |
|---|---|---|
| verified 872, class `(25,0,0)`, `e = 25`, `S = 4`, `X4 = 0` | §2.5, §4.4 | Algorithm A leaves **1** configuration, and it is exactly the real 872's shape: `a1 = 4` (all length 5), `c1 = 25` type-I cycles, `a2 = a3 = c2 = 0`, `n45 = 4`, `n4 = 0` |
| verified 873s, class `(0,6,0)`, `e = 0`, `S = 24`, `X4 = 6` (`X4h = 5`) | §2.5 | survives at its real `X4h = 5` (and at `X4h = 6`); the system additionally forces `X4h ≥ 5` there, a correct sharpening on a real object |
| `(10,2,0)`, `e = 2`, `X4h = 2` (the sibling of the Lemma-5.8 cell) | §2.5 | **4** configurations survive — the registered count.  The cell is emptied only at `X4h = 1` |
| type-II admissibility outside the 871 budget | §4.6 | `c2 ≥ 1` survives at `(25,0,0)`, `e = 3…11`, and at 30 `(D,e)` cells with `D ∈ {25,30}` |
| engine-level type-II control | `n6c2probe` | type-II-capable engine regresses node-for-node with the extension off and finds a planted type-II census SAT |
| cap-mode robustness | §4.5 | dropping the un-re-derived `g(20) = 25` changes no verdict and keeps every control alive |
| mirror fidelity | `logs/diffcheck.log` | survivor-set equality with `tight_enum.py` on 16 habitat + 6 control cells; `F` agreement over the consumed range |

## 6. Case-table sizes (for the paper appendix)

| table | rows | file | appendix-suitable |
|---|---|---|---|
| Lemma 5.8, census level | 5 | `logs/lem58_k1.log` §A | yes |
| Lemma 5.8, closed-form level | 4 | `logs/lem58_k1.log` §A2 | yes |
| Lemma 5.8, deciding candidate | 1 | `logs/lem58_k1.log` §C | yes |
| Lemma 5.8, every candidate + witness | 4 804 (both X4h) | `logs/lem58_full_table.log` | no (supplementary) |
| Lemma 5.9, branch level | 5 | `logs/lem59_z1.log` §A | yes |
| Lemma 5.9, every wiring + refinement | 26 | `logs/lem59_z1.log` §B,§C | yes |
| Lemma 6.7, Tier 1 (`c2 ≥ 1`) | 150 | `logs/lem67_c2.log` §A | yes (or the 11-row Tier 2 alone, with a one-line Tier-1 rule) |
| Lemma 6.7, Tier 2 (`c2 ≥ 1`) | 11 | `logs/lem67_c2.log` §B | yes |
| Lemma 6.7, `a3 ≥ 1` clause | 150 (146 + 4) | `logs/lem67_c2.log` §G | yes |
| Lemma 6.7, per-class tallies | 16 | `logs/lem67_c2.log` §C | yes |
| Lemma 6.7, every candidate + witness | 54 233 | `logs/lem67_full_table.log` | no (supplementary) |

The recommended paper appendix is: sect. 2.2's three small tables, sect. 3.5's
two wiring tables, and sect. 4.1's closed-form rule with sect. 4.2's 11-row
Tier-2 table — about 45 printed rows in total, with the two large per-candidate
files cited as supplementary data.

## 7. What this does and does not settle

**Settled.**  All three lemmas now have complete derivations: every rejection
test is a proved necessary condition for *every* first-occurrence ordering in
the class (sect. 1.3, sect. 3.3), the enumerated candidate spaces are proved
supersets of what real length-871 orderings induce (sect. 1.1, sect. 3.7), and
the eliminations are printed in full.  A reader can re-derive Lemma 5.8 and
Lemma 6.7 by hand from the tables and the capacity table alone, and Lemma 5.9
from the fourteen `F`-values.

**Corrections to the paper's prose** (none affects a theorem statement):

1. Lemma 5.8's supporting text should drop the claim that both the run cap and
   the frontier are needed; the class budget plus the frontier suffices
   (sect. 2.4).  `F(2,8,0,0) = 20`, not 21.
2. Lemma 5.9's supporting text should cite the mechanical wiring enumeration,
   not a hand list, and may quote the sharper `F(2,15,2,1) = 24` for the `zq`
   branch.
3. Lemma 6.7 should be stated with the Tier-1 closed form `N_lo > N_hi`, which
   makes 140 of the 150 censuses checkable by inspection, and should record
   that its `a3 = 0` clause is proved by the same two tiers.
4. The paper's phrase "reproduced independently" should be replaced by the
   specific evidence: four independent enumerations of the frontier, R-n6-6's
   independent re-derivation of both kills, and the differential certificate
   of `checks/diffcheck.py`.

**Assumed, not re-proved here.**  The imported stock of sect. 0 — the counting
identities, `E1`/`E2`, the `C6-A`/`C6-B` finite certifications, and the rigid
structure lemmas `TC1`–`TC4` of PAPER §6.1 (reviewed sound by R-n6-6).  These
are the inputs the paper already carries; this document adds nothing to and
subtracts nothing from their status.
