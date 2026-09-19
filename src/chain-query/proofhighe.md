# proofhighe.md — the high-e cells of the L = 871 habitat are EMPTY

T-n6-highe (`approaches/n6highe`), 2026-09-03.  **n = 6 ONLY; every constant
is an n = 6 constant.**

**Scope.**  The six cells of the registered L = 871 habitat (THEOREM N871-B,
T-n6-871, reviewed R-n6-4) with the largest exhaustion trees:
corner (20,0,0) at e in {5,6,7,8,9} and corner (15,1,0) at e = 7.
This artifact proves all six EMPTY.

**Imported (registered; cited, not re-proved).**  The n = 6 stock of
`approaches/n6/proof6.md` (T0, THMM, PNUM, UNIT, LEDGER, T1, T2, LEMMAS, L12,
LU8, E1, E2, E3, LEMMAC, T7, DEFSPLIT, LEMMAA, PARETO, LEMMAR, L1, L1a, L2);
the three lemmas and certified chain constants of
`approaches/n6-871/proof871.md` (PARETOS, CHAINRUN, GROUPS; C6-A-871 run caps
4/2/interior-0, C6-C-871 coarse Pareto to cost 20, C6-S-871 refined frontier
gS, and the CORRECTED alternation accounting of its §7 item 5); the certified
fact that rho has order EXACTLY 5 on every one of the 720 permutations with no
smaller period (`n6lowe` `src/blockcheck`, `rho_order5=720/720`,
`failures=0`); and THEOREM N871-B itself, which pins every length-871
superpermutation to rung 4 (W = 146, slack = 0) and to the 16 registered
(corner, e) cells.

**Cell-local constants.**  In corner (20,0,0): (D,X4,Z) = (20,0,0), P# = 28,
h = 27 - e, all heavy transitions have d = 3.  In corner (15,1,0):
(D,X4,Z) = (15,1,0), P# = 27, h = 26 - e, exactly one transition has d = 4
(X4h = 1) and the rest of the heavies have d = 3.  slack = 0 and LEMMAS-n6
give Q2 = zp2s = 0; Z = 0 gives zq = zh = zp3 = zp2s = zp2g = 0, hence
cnl = e (T1-n6) and pshits = e (T2-n6).

---

## 1. Standing facts at Z = 0, Q2 = 0 (all six cells)

**Fact 1.1 (every heavy is a chain-boundary entry).**  At Z = 0 every heavy
transition is a COMPLETION exit (zp3 = 0) landing on a crit (zh = 0); a crit
entered by a d >= 3 transition heads its link-path (its class has no in-link,
because a link lands exactly on the crit and each permutation is entered
once).  The d = 3 heavies are therefore exactly the HOPS, and the d >= 4
heavies (X4h of them) head chains.  Counting chain heads: q_1 (a crit at
zq = 0, heading its path and chain) + the e ps-hits (E1-n6) + the X4h heavy
d >= 4 entries; so **NCh = e + 1 + X4h exactly**, and chain tails partition as
q_720 + the e CNLs (E2-n6) + the X4h d >= 4 exits.

**Fact 1.2 (CYC5: every pointer cycle has exactly 5 vertices).**  Along a
pointer edge the run start advances by rho (L2).  A cycle of j vertices
closes: rho^j(s) = s.  rho has order exactly 5 on every permutation and no
smaller period (certified, `blockcheck`), so j = 5. []

**Fact 1.3 (NCFLOW: nc-runs carry one cnl in-edge and one ps out-edge).**
At Z = 0, Q2 = 0 all e premature run ends exit as premature-sig edges landing
on crits (ps-hits; T2-n6 with Q2 = zp3 = zp2g = 0).  Each such edge's pointer
TAIL is the run starting at rot(z), a non-crit start (L12-n6's argument), and
distinct z give distinct tails; e edges on e nc-runs is a bijection: **every
nc-run has a ps out-edge**.  Dually, at Z = 0 every nc-run is CNL-entered
(LU8-n6 STEP 1).  So in the pointer graph, every nc-run has in-degree and
out-degree exactly 1, its in-edge a cnl (tail a crit-run), its out-edge a ps
(head a crit-run): **no component has an nc-run source or sink, and nc-runs
never touch** (no nc->nc edge needs zp2g > 0). []

**Fact 1.4 (component shapes).**  By Fact 1.3 every component alternates
crit-chains and SINGLE nc-runs, beginning and ending (if a path component)
with a crit-chain.  Hence, with m_g the number of link-paths whose crit-chains
lie in component g and k_g its nc-runs:

    path component:  k_g = m_g - 1 exactly,  sum of its path lengths <= 6 - m_g
                     (component size <= 5, L2), so m_g <= 3, and m_g = 3
                     forces three length-1 paths;
    cycle:           k_g = m_g, and by Fact 1.2 its size is EXACTLY 5, so
                     sum of path lengths = 5 - m_g and m_g in {1,2}:
        T1: ONE path of length 4 (deficiency 1) + one nc-run;
        T2: TWO paths of lengths {1,2} (deficiencies {4,3}) + two nc-runs. []

**Fact 1.5 (cycle paths are pinned singleton chains).**  In a cycle every
crit-chain's head is entered inside the cycle and the entering edge can only
be a ps (LEMMAC-n6's argument: not a link — the head would not head a path —
and not a cnl — cnl heads are nc-runs); every crit-chain's end has its
out-edge inside the cycle landing on an nc-run, i.e. a cnl.  So EVERY path of
a cycle is ps-headed and cnl-ended: a SINGLETON hop-chain with both endpoint
types short, of pinned composition: a T1 path is a singleton of cost exactly
1 counted by S5; each T2 path is a singleton counted by S4, the two costs
being {4,3}. []

---

## 2. ENDS-n6 — the kk = 1 endpoint coupling

Write npin = c1 + 2*c2, where c1 / c2 are the numbers of T1 / T2 cycles, and
kk = e - npin (the number of nc-runs in PATH components).

**ENDS-n6.  At Z = 0, Q2 = 0 with kk = 1, the unique path component holding
an nc-run has exactly two crit-chains: [P1] --cnl--> [nc] --ps--> [P2], with
l(P1) + l(P2) <= 4.  P2 is the FIRST link-path of the unique remaining
(non-cycle) ps-headed hop-chain, and P1 is the LAST link-path of the unique
remaining cnl-ended hop-chain; both have length <= 3, and their deficiencies
sum to >= 6.  (More generally, at any kk every non-cycle ps-headed chain's
first path and every non-cycle cnl-ended chain's last path has length <= 3.)**

*Proof.*  Each T1 cycle contains exactly one ps edge and one cnl edge, each
T2 exactly two of each (Facts 1.4, 1.5), so cycles consume npin of the e ps
edges and npin of the e cnls.  The remaining kk ps and kk cnl edges are
incident to the kk nc-runs of path components (Fact 1.3: each nc-run carries
exactly one of each).  At kk = 1 both attach to the single non-cycle nc-run,
whose component has k = 1, hence m = 2 (Fact 1.4) and size
l(P1) + 1 + l(P2) <= 5.  The ps edge's head is a path-head crit (E1-n6):
that path is P2 (the crit-chain after the nc), it heads its chain, and
l(P2) <= 5 - 1 - l(P1) <= 3.  The cnl edge's source is the end completion of
P1's last class (E2-n6): P1 ends its chain, l(P1) <= 3.  Deficiencies:
(5 - l1) + (5 - l2) >= 10 - 4 = 6. []

**What it buys.**  The certified refined frontier gS indexes chains only by
(cost, s5, s4, first-short, last-short); "short" is length <= 4.  ENDS-n6
pins the first/last path LENGTHS of the obligated chains, a strictly finer
datum, and couples them across the two obligated chains through l1 + l2 <= 4.
Whether a chain with pinned endpoint lengths and a given block count exists
is decidable by a tiny exhaustive enumeration (`checks/chainq.c`, WLOG head
123456, adapted from the registered `chains871.c`).  `checks/qvalid.py`
validates `chainq` against the registered certified gS literal over the
DECISIVE range -- every table row with cost <= 16, all four typed maxima
(free / first-short / last-short / both-short) mapped onto endpoint-LENGTH
pinned queries: [stat:qvalid_rows=186] rows, [stat:qvalid_maxima=741] typed
maxima, [stat:qvalid_queries=7855] queries, ZERO disagreements
(`logs/qvalid.log`).

---

## 3. QUADCOVER-n6 — the cycle class-sets must tile the leftover

**QUADCOVER-n6.  At Z = 0, Q2 = 0, the class set of each T1 cycle's link-path
is a rho-4-segment {C(x), C(rho x), C(rho^2 x), C(rho^3 x)} for some
permutation x (L1), the class sets of distinct cycles and of the non-cycle
chains are pairwise disjoint, and together they partition the 120 classes.
Hence, for a profile whose cycles are all T1 (c2 = 0), once the non-cycle
chains are fixed, the leftover classes must admit a partition into Ncyc
rho-4-segments.  This is a NECESSARY condition on the non-cycle chains'
class sets.** []

`checks/cover.c` enumerates EXHAUSTIVELY every non-cycle chain configuration
of a decomposition (chain 1's head crit fixed to 123456 -- relabelling is
free and transitive, so every configuration has a representative with the
designated chain's head there; chain 2, where present, from every head) and
checks the partition by exact cover over all rho-4-segments inside the
leftover.  POSITIVE CONTROL: the verified 872's shape -- one free chain of 4
full paths + 25 T1 cycles -- comes back ALIVE (`cover 25 0 0 0 0 0 4`:
covers=1, `logs/cover_final.log`), so the machinery accepts the real object.

---

## 4. THE RESULTS

**THEOREM HIGHE-1.  No superpermutation on [6] of length 871 lies in any of
the six cells (20,0,0) e in {5,6,7,8,9} or (15,1,0) e = 7.  Together with
the registered N871-B this reduces the L = 871 habitat to the ten cells
(10,2,0) e=2; (15,0,1) e=2; (15,1,0) e in {1,2,3,4}; (20,0,0) e in
{1,2,3,4}.**

*Proof sketch (every step machine-checked; see §5 map).*  By N871-B any such
string has W = 146, slack = 0, and its profile is one of the
[stat:profiles=14] admissible profiles of the six cells under the full
registered guard set (`checks/profiles.py`, `logs/profiles.log`).  All have
Z = 0, Q2 = 0, so Facts 1.1-1.5, ENDS-n6 and QUADCOVER-n6 apply.
* [stat:killed_fh=2] profiles ((20,0,0) e=5 Ncyc=3 and e=6 Ncyc=4) die
  against the pinned cycle types + component shapes + forced short-3
  endpoints wired into the chain economy (`checks/scanhigh.py`,
  `logs/scanhigh2.log`).
* [stat:killed_ends=9] profiles die by ENDS-n6: enumerating every (c1,c2)
  split, every coupled chain decomposition (same-chain and split-chain), and
  querying the exhaustive enumerator: no chain configuration reaches the
  required block totals (`checks/killer.py`, `logs/killer1.log`,
  [stat:queries=5544] chainq queries, ~40 s).  This alone empties
  (20,0,0) e = 5, 8, 9.
* [stat:killed_cover=3] profiles survive the chain economy but die by
  QUADCOVER-n6: their surviving decompositions are UNIQUE up to block split
  ((A) e=6 Ncyc=6: one 22-block cost-14 chain; (B) e=7 Ncyc=6: two
  decompositions; (C) (15,1,0) e=7 Ncyc=7: two 10-block cost-4 chains); the
  complete exact-split sweep (`checks/bfinal.py`, `logs/bfinal.log`) runs
  `cover` on every configuration: every enumeration is EXHAUSTED with zero
  quad-partitions (`logs/cover_final.log`: configs 2 / 19 / 19 / 19, covers
  0 / 0 / 0 / 0). []

---

## 5. CONTROLS AND VERIFICATION MAP

**Controls (mandatory; all pass).**
* The verified 872 (its own length, rung 5, cell (25,0,0) e=25): profile
  still admissible under every new guard (`logs/scanhigh2.log`), its shape
  passes QUADCOVER as a positive control (covers=1), and every new lemma is
  asserted clause-by-clause on the REAL string by the independent analyser
  `checks/validate_obj.py` (`logs/validate_obj.log`): e=25, Z=0, Q2=0,
  Ncyc=25, ALL 25 cycles have exactly 5 vertices, all T1, k=m, and the 4
  path components have k = m-1.  Zero violations.
* The verified 873 (e = 0): no cycles, no premature ends; every new lemma is
  vacuous or passes; its cell stays admissible.
* Scope: every kill above is at LENGTH 871 (rung-4 profiles of the six
  cells); nothing here constrains e at any other length.

| step | code | log | result |
|---|---|---|---|
| profile extraction (full registered guard set) | checks/profiles.py | logs/profiles.log | 14 profiles, 6 cells |
| new-guard scan (Facts 1.1-1.5 wired) | checks/scanhigh.py | logs/scanhigh2.log | 12 profiles left; controls OK |
| chainq vs certified gS (cost <= 16, all typed maxima, endpoint-pinned) | checks/qvalid.py | logs/qvalid.log | 186 rows / 741 maxima / 7855 queries, 0 disagreements |
| ENDS-n6 kills | checks/killer.py + chainq.c | logs/killer1.log | e=5,8,9 empty; 9 profiles dead |
| decomposition lists | checks/blist.py | logs/blist.log | (B): 2 decompositions |
| exact-split sweep + QUADCOVER | checks/bfinal.py + cover.c | logs/bfinal.log, logs/cover_final.log | (A),(B),(C) EMPTY |
| positive control (872 shape) | checks/cover.c | logs/cover_final.log | ALIVE (covers=1) |
| object-level lemma validation | checks/validate_obj.py | logs/validate_obj.log | 872 + 873: zero violations |

Total compute: under 10 CPU-minutes beyond the registered artifacts (the
largest single run is the extended qvalid sweep, ~4 CPU-minutes; every
decisive kill re-verified under the final chainq binary with identical
verdicts).

---

## 6. HONEST NEGATIVES, GAPS, SCOPE

1. **The six kills lean on the registered stock.**  N871-B (habitat),
   LEMMAS-n6 (Q2 = 0 at slack 0), the certified chain constants, and the
   registered profile enumeration (`scan871.py`) are all load-bearing
   imports.  Any of them falling reopens these cells.
2. **`cover.c`'s partition check is NECESSARY, not sufficient.**  A passing
   configuration would not prove a superpermutation exists; only emptiness
   is claimed, so this direction is sound.
3. **WLOG discipline.**  chainq/cover fix the designated chain's head crit at
   123456; relabelling (free, transitive, commutes with rot/rho/sig/d) makes
   this lossless.  For two-chain profiles chain 2 runs over all 720 heads.
4. **killer.py's split-chain search checks only the maximal feasible block
   count of the ps-chain per split** -- sound because lowering it only
   raises the cnl-chain's requirement (monotone); the exact-split sweep for
   the surviving profiles (`bfinal.py`) has no such shortcut.
5. **kk >= 2 is not covered by ENDS-n6's implementation** (the guard
   abstains there).  No surviving profile of the six cells has kk >= 2 after
   Facts 1.1-1.5; the two kk=2 profiles died in `scanhigh.py`.
6. **What was tried and did NOT bite on its own**: CYC5 + pinned cycle types
   alone (0 cells; `logs/scanhigh1.log`); they became decisive only combined
   with NCFLOW's k = m-1, the exact head/tail matching, ENDS-n6, and
   QUADCOVER-n6.
7. **Review R-n6-8 repairs (verdict-neutral, applied).**  (R1) the
   object-level validator's T1/T2 check contained a vacuous expression; it
   now computes each cycle's crit-chain lengths explicitly and additionally
   asserts SING and SHORT3 per component (re-run: zero violations).  (R2)
   profile A's cover run is regenerated by the committed driver
   `checks/bfinal.py` (with the positive control asserted) rather than an
   ad-hoc invocation.  (R3) qvalid originally covered cost <= 10 free-typed
   entries only; it now covers the full decisive range (above).  `chainq.c`
   also gained a sharper sound prune (each future {4,5}-run needs a distinct
   remaining short separator, so additional blocks <= (4 - runlen) + 5*r4);
   killer.py and bfinal.py re-ran under the patched binary with IDENTICAL
   verdicts.
8. **The remaining habitat is the ten low-e cells**, exactly the cheap end
   of decide871's cost table (e <= 4).  The teeth here (ENDS at kk = 1,
   QUADCOVER) apply there too in principle but the low-e profiles have many
   more admissible decompositions; nothing is claimed about them here.
