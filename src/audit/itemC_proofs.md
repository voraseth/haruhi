# itemC_proofs.md — T-n6-auditC proofs and verdicts

## C2 — the X4h error (referee finding 4). VERDICT: CONSERVATIVE RELAXATION — PROVED.

Definitions (proof871.md line 43, PAPER line 320): for the multiset of
transition costs d >= 2, X4 = sum_{d>=4}(d-3), X4h = #{d>=4}.

**Fact C2.0 (X4h <= X4, and the feasible window).** Each heavy transition has
cost d in {4,5,6}: d >= 4 by definition of heavy, and d <= 6 because
d(p,q) = 6 - |longest suffix of p that is a prefix of q| <= 6
(proof871.md §1, which defines d and states only that transitions are the
steps with d >= 2 -- it asserts NO upper bound of 5).  Cost-6 transitions
are real, not merely formally admissible: in the string 123456234615 the
only permutation windows are 123456 at position 1 and 234615 at position 7,
and d(123456,234615) = 6.  Hence each heavy contributes d-3 in {1,2,3} to
X4, so with X4h heavies:  X4h <= X4 <= 3*X4h, i.e.  ceil(X4/3) <= X4h <= X4,
with X4h = X4 iff every heavy has d = 4.
(CORRECTION.  An earlier version of this Fact claimed d in {4,5} "because a
transition cost in the n=6 chain graph is at most n-1 = 5", and attributed
the range d in {2,...,5} to proof871.md §1.  Both were wrong: the cost bound
is 6, and proof871.md §1 asserts only d >= 2.  The correction is
verdict-neutral -- no executed line anywhere tests a LOWER bound on X4h
(the scanner pins X4h := X4, its maximum, and X4h occurs only on the RHS of
the two <=-caps O2/O3), and every stage that takes X4h as a cell parameter
runs at X4 <= 2, where ceil(X4/2) = ceil(X4/3).  Re-running the scan with
X4h widened all the way to [0, X4] reproduces the committed survivor sets
byte-identically at L = 868..873.)  (This is the referee's inequality;
equality is NOT available at Algorithm-2 stage — Lemma 5.8 proves it only
later, for surviving 871 profiles.)

**Occurrence census.** `grep -rn X4h` over all executed sources
(approaches/n6-871/checks/, github-n6-872/src/) — the two trees are
byte-identical for scan871.py (diff rc=0).  Every occurrence:

| # | file:line | role | test | side X4h is on | increasing X4h... | X4h -> X4 substitution |
|---|-----------|------|------|----------------|-------------------|------------------------|
| O1 | scan871.py:685 | `for X4h in range(X4, X4+1)` | (the substitution itself) | — | — | — |
| O2 | scan871.py:686 (guard t7) | rejection cap | NCh <= NChcap = T7_BASE + X4h + zh + cnl | RHS, coeff +1 | RAISES the cap -> WEAKENS rejection | CONSERVATIVE |
| O3 | scan871.py:688-690 (guard lemmaR) | rejection caps | Fp+S5 <= 4*Rcap and S5 <= 2*Rcap, Rcap = 1 + X4h + zh + cnl + S4 | RHS, coeff +1 | RAISES both caps -> WEAKENS rejection | CONSERVATIVE |
| O4 | scan871.py:720 | witness-dict record `X4h=X4h` | not a test | — | none | neutral (but see O5/O6 consumers) |
| O5 | scanhigh.py:118 (Algorithm 3) | `X4h = w['X4h']` | DEAD READ — the variable is never referenced again in highe_ok (grep: only lines 15,16 comments +118) | — | none | neutral |
| O6 | tight_enum.py:51,53,62 (class elimination), c2_witness.py, differential.py, driver.py | NCh = e+1+X4h (TC1, an EQUALITY) | equality, so NOT covered by monotonicity | — | — | NOT a substitution site: these stages take X4h as an input CELL PARAMETER and the drivers ENUMERATE it over the feasible window of C2.0: (20,0,0) cells have X4=0 => X4h=0 forced; (15,1,0) has X4=1 => X4h=1 forced (one heavy, d=4); (10,2,0) is run at BOTH X4h=1 and X4h=2 (tight_enum.py:118-119) = full window; the 873 control is run at X4h in 2..6 = exactly the corrected window [ceil(6/3),6] = [2,6] (tight_enum.py:107-110, asserts the real X4h=5 corner survives) |
| O7 | validate871.py:85,184 | independent validator computes TRUE X4h from the string and asserts T7 with it | — | — | correct semantics (control-side evidence) |

No other executed occurrence exists.  Paper-side occurrences (PAPER lines
650, 682, 686, 1148, 1167, 1169) restate O2/O3/O6.

**Lemma C2.1 (relaxation lemma).** Let W_true(cell) be the set of admissible
(profile, X4h) pairs when X4h ranges over the true window [ceil(X4/3), X4]
of C2.0, and W_run(cell) the set computed by the executed scanner with
X4h := X4.  Then a cell is empty under W_run only if it is empty under
W_true; hence every cell the scan kills contains no realizable configuration.

*Proof.* Only guards t7 (O2) and lemmaR (O3) mention X4h, and in both it
appears with coefficient +1 on the right-hand side of a <=-cap; every other
guard is X4h-free.  So for fixed remaining profile coordinates, the pass-set
of each X4h-bearing guard is monotone nondecreasing in X4h, and X4h = X4 (the
max of the window, by C2.0) is the pointwise weakest instance: if ANY
X4h in the window passes, X4h = X4 passes.  The NCh enumeration range
[1, min(Pn, NChcap)] likewise grows with X4h, so the ranges scanned at
X4h = X4 contain those at the true X4h; in particular the true NCh of any
realizable configuration (which satisfies T7 with its true X4h, per proof871
§T7 / validate871.py:184) lies inside the scanned range.  Hence
W_run nonempty <=> W_true nonempty, and in the completeness direction
W_true nonempty => W_run nonempty.  A realizable configuration yields a
member of W_true (its guards hold with true X4h by the already-audited guard
lemmas), hence a member of W_run; contrapositive gives the claim.  QED.

Note the equality direction too: because X4=max window and monotone, the
survivor CELL SETS are provably identical, not merely nested — confirmed
computationally below.

**Downstream soundness (O5/O6).** Algorithm 3's executed code never uses the
(possibly overstated) w['X4h'] (dead read, O5).  The class-elimination stage
(O6) uses NCh = e+1+X4h as an equality but quantifies X4h over the full
feasible window per cell (or the window is a single forced point), so no
completeness loss enters there either; its 873 control at the true X4h=5
survives (tight_enum.py:110 assertion).  Therefore the paper's misstatement
"X4h = X4" in Algorithm 2 is a PRESENTATION error in the paper, not a
soundness gap in the executed proof: the referee's conservative-relaxation
hypothesis is PROVED.  Required paper fix: replace "set X4h = X4" with
"upper-bound X4h by X4 (valid by X4h <= X4, Fact C2.0); Lemma 5.8 later
upgrades this to equality on survivors".

**Checker (committed).** checks/itemC_x4h_check.py textually patches the
single substitution site to the true window ceil(X4/3)..X4, re-runs
scan_length for L = 868..873 under the DEFAULT guard set (which contains
both X4h-bearing guards t7, lemmaR), and diffs survivor cells.
Result (logs/itemC_x4h_check.log, 3.3 s):
  L=868..873 survivor cells IDENTICAL under both semantics
  (0, 0, 8, 63, 219, 503 cells respectively);
  CONTROL verified-872 cell (25,0,0) e=25 alive under both;
  CONTROL verified-873 cell (0,6,0) e=0 alive under both.  PASS.

---

## C1 — Paper Lemmas 5.2, 5.3, 5.4. No undischarged (c): all three are discharged.

The paper's "short counting arguments" sentence (PAPER line 571) is inadequate
as presentation, but complete proofs EXIST in the project artifact
approaches/n6-871/proof871.md (sections 3, 4, 5), written from the raw
definitions of proof871.md §1 (= proof6.md §1) plus the registered, reviewed
stock of approaches/n6/proof6.md (E3-n6 line 272, LEMMAC-n6 line 299, L12-n6
line 279, L2 line 176, run taxonomy 2(c)).  I re-audited each proof step by
step; findings and classifications follow.  Fix required of the paper: cite or
inline these proofs; the one-sentence gloss is what the referee rightly
rejected.

### Lemma 5.3 (Refined chain bookkeeping, CHAINRUN-n6) — VERDICT (b) FINITE-CHECK, sufficiency PROVED.
Source: proof871.md §4 + §2 (C6-S-871); code `_maxblocks`/`build_chaintypes`/
`FC`/`FCs` in scan871.py.
* The load-bearing content (per proof871.md §4 "MEASURED" note and the §7
  ablation) is (i) the certified refined frontier gS and (ii) the exact global
  bookkeeping P#=sum blocks, D=sum cost, S5=sum s5, S4=sum s4.
* (ii) is PROVED: link-paths partition into hop-chains (each path lies in
  exactly one maximal hop-joined sequence, by the registered chain
  definition), and cost=total deficiency, length-4 paths contributing 1,
  short paths 5-l in {2,3,4}; hence also s5+2*s4 <= c <= s5+4*s4 per chain.
  Audited: correct.
* (i) is a FINITE CHECK.  Checked range: gS(c,s5,s4,a,b) for ALL c <= 18,
  exhausted by the independently written enumerator checks/chains871.c mode S
  in 8,296,793,311 nodes (logs/paretoS18.log, MODES CMAX=18); coarse table
  g(c,a,b) exhausted to c <= 20 (logs/pareto20.log, 778,723,993 nodes);
  C6-A run caps (4 paths/run, <=2 length-4, no interior 4) exhausted over all
  720 heads (logs/chainsA.log, RUNCAP4 PASS).
* SUFFICIENCY (no ordering falls outside the check) — the argument the
  paper omits, discharged here:
  1. WLOG head = 123456: alphabet relabelling acts letterwise, commutes with
     rot, rho, sig and with d (suffix-prefix matching is preserved by any
     letter bijection), and is transitive on S_6; the recorded statistics
     (cost, s5, s4, a, b, blocks) are relabelling-invariant.  (Mode A re-ran
     over all 720 heads for C6-A as a cross-check.)  Audited: correct.
  2. Range coverage: in the habitat of Prop. 5.5 and the 871 scan, a single
     chain's cost c <= D <= 20 (L <= 871 => B = D/5+X4+Z <= 4 => D <= 20), and
     scan871.py consults the gS table ONLY for c <= REFINED_CMAX = 18
     (build_chaintypes line ~485); for c in {19,20} it uses only the certified
     coarse cap and the PROVED _maxblocks bound, and beyond CAP_CMAX the
     proved typed-value-cap formula 4-2a-2b+2c.  So a table MISS at c <= 18
     ("absent = unrealizable") is backed by the exhaustive enumeration, and
     no realizable chain is ever rejected by an out-of-range lookup.
  3. The auxiliary combinatorial inequality (r <= s4+1-a3-b3, blocks <= s4+4r,
     s5 <= 2r, r=0 => s5=0) is PROVED in proof871.md §4; I audited the
     separator argument (two maximal {4,5}-runs are separated by a short path;
     a leading/trailing short path is not a separator; a contiguous
     subsequence of a hop-chain is a hop-chain, so C6-A applies per run) —
     correct; and _maxblocks implements exactly it (case r<1 forces s5=0,
     v=s4; singleton a=b=1, s5+s4=1 => 1 block).  Verdict-neutral over
     L=868..873 per §4, but proved regardless.
* Program-verification evidence: chains871.c is an independent
  reimplementation agreeing entry-for-entry with the registered C6-C table;
  validate871.py asserts every CHAINRUN clause (r-inequality, blocks cap,
  RUNCAP/RUNFOURCAP/interior-four, maxblocks) per chain on real orderings.

### Lemma 5.4 (Component packing, GROUPS-n6) — VERDICT (a) PROVED.
Source: proof871.md §5, clauses (i)-(v); code `_group_types`/`_gfeas`/
`groups_feasible` in scan871.py.  Audited step by step:
* Degrees <= 1 and no loops (rho fixed-point-free), so components are directed
  paths/cycles; L2 (pointer edges advance run starts by rho, order 5; run
  starts distinct) caps components at 5 vertices.  Correct.
* (i) Ncomp = P# - cnl + Q2 + zp3 + Ncyc: Euler count V-E with V = 120+e
  (proof6.md 2(c)) and E = (120-P#) links + cnl CNLs + (e-Q2-zp3)
  premature-sig edges.  Correct given the registered exit taxonomy.
* (ii) crit-chains never leave a component (links are pointer edges); vertex
  split sum_j l_{g,j} + k_g <= 5.  Correct.
* (iii) k_g >= m_g - 1 (>= m_g on cycles): a path-head crit-run's in-edge can
  only be a ps-hit whose tail is an nc-run (not a link — heads are not
  link-entered; not a CNL — CNLs land on non-crits; S-exits give no edge),
  and rot(z) is a non-crit start for premature z (L12-n6's injectivity-of-rot
  argument); distinct heads consume distinct nc-runs (out-degree <= 1).
  Correct.
* (iv) partition identities — definitional.  (v) m_g = 0 components consume
  zp2g edges and their path-sources consume distinct zq+zh+zp2s units —
  correct against the registered pool taxonomy.
* Completeness of the type enumeration: m_g <= 3 because sum l >= m_g and
  k_g >= m_g-1 give 2m_g-1 <= 5 — proved inline; _group_types enumerates all
  (m,k,lengths) with size <= 5.  No finite-check residue beyond trivial
  enumeration of integer partitions of <= 5.
* Machine evidence: validate871.py asserts (i), component size, vertex split,
  k_g bound, GROUPTYPES membership, zp2g/source budgets AND groups_feasible
  itself on every corpus ordering.

### Lemma 5.2 (Singleton-chain bound, PARETOS-n6) — VERDICT (a) PROVED
(with one certified-table dependency shared with 5.3).
Source: proof871.md §3; code `Fs`/`FCs` in scan871.py.  Audited:
* Ns >= max(0, SH+ST-Sp) is E3-n6 and Ns >= Ncyc-zp2g is LEMMAC-n6 — both
  registered and reviewed (proof6.md §6, review Rn6-2); hence Ns >= PEN.
* A singleton short chain has 1 block, cost 5-l in 1..4, endpoint types
  a=b=1, so it discharges one a- and one b-obligation — correct from the
  definitions.
* The remaining NCh-PEN chains are capped by the C6-C frontier g(c,a,b)
  (certified to cost 20, value-cap formula beyond — same sufficiency argument
  as in 5.3 item 2); the code's running-max envelope over costs <= c is a
  further upper-bound relaxation, hence sound.  Monotonicity claim of the
  paper is used only in this conservative envelope form.
* P# = sum blocks, D = sum cost: the partition identity again.  Correct.

### Controls (both items)
checks/itemC_lemma_controls.py runs the full clause-level validator
(validate871.check) on the verified 872 (shared/best872.txt) and on ALL 96
verified optimal 873s (github-n6-872/data/optimal-873/): 97/97 pass every
clause of 5.2/5.3/5.4 and the imported stock (logs/itemC_lemma_controls.log,
0.5 s).  The 872 has e=25, S5=25, X4=0, Ncyc=25; the 873s have X4=6 with TRUE
X4h=5 — a real ordering on which X4h < X4 strictly, witnessing that the C2
substitution is a proper relaxation and still conservative (the 873 cell
survives both semantics, itemC_x4h_check).  Also the registered project-level
control: proof871.md Remark — every inequality of 5.2-5.4 holds with equality
on the 872 witness, so none can be strengthened without falsifying it.

### Consequence for Proposition 5.5 (exclusion of length 870)
Prop 5.5 = the finite scan with guards {chainrun, groups} added, recorded in
proof871.md §6 (CHAINRUN+GROUPS is the unique minimal sufficient pair; ablation
table §7).  With 5.3 discharged as (b)-with-sufficiency and 5.4 as (a), and the
C2 substitution proved conservative, the inputs to Prop 5.5 are established;
its own content is the finite feasibility computation, independently
reimplemented (scan871.py vs scan6.py, byte-identical ladders) and rerun
pristine in review Rn6-4.
