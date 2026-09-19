#!/usr/bin/env python3
"""tier_check.py -- INDEPENDENT verification of T-n6-fin's two-tier hand
derivation of  c2 = 0  and  a3 = 0  (src/finlem/finlem.md sect. 4).

I re-derive the two tiers from MY OWN statements of the necessity lemmas
(coverage.md Lemmas 4.9, 4.10, 4.11) and MY OWN capacity function
(checks/pareto.py), and check:
  (i)   the Tier-1 closed form is algebraically what my Lemmas 4.9/4.10 give;
  (ii)  the census box ranged over is the box of my Algorithm G (sect. 3);
  (iii) the published tallies 140+10 (c2>=1) and 148+2 (a3>=1) reproduce;
  (iv)  0 survivors, so c2 = 0 and a3 = 0 for every real length-871 ordering;
  (v)   the derivation does NOT depend on g(20)=25 (cap-mode 'lin' rerun);
  (vi)  discrimination: the same two tiers ADMIT c2>=1 outside the 871 budget.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("tier_check: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import sys, os, math
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from pareto import F, g, NEG
from census_gen import Z0_CLASSES, configs_of_cell


# the 16 Z=0 cells of the habitat BEFORE Theorem K1 removes (10,2,0)/X4h=1
CLASSES16 = ([(20, 0, e, 0) for e in range(1, 10)] +
             [(15, 1, e, 1) for e in (1, 2, 3, 4, 7)] +
             [(10, 2, 2, 1), (10, 2, 2, 2)])

fail = 0
def check(n, ok, x=''):
    global fail
    print(f"  [{'PASS' if ok else 'FAIL'}] {n}{(' :: ' + x) if x else ''}")
    if not ok: fail += 1

def censuses(D, X4, e, X4h):
    """the (a2,a3,c1,c2) box of Algorithm G, sect. 3 tests G2/G3 only."""
    P = 24 + D//5
    for a2 in range(e + 1):
        for a3 in range((e - a2)//2 + 1):
            for c2 in range((e - a2 - 2*a3)//2 + 1):
                c1 = e - a2 - 2*a3 - 2*c2
                a1 = P - e - a2 - a3
                if c1 < 0 or a1 < 0: continue
                yield (a2, a3, c1, c2, a1, P)

def tier1(a1, a2, a3, c1, c2, lam):
    """N_lo from my Lemma 4.10 (class budget), N_hi from my Lemma 4.9 (run cap)."""
    N_lo = -((-(120 - 3*a1 - 4*a2 - 3*a3 - 4*c1 - 3*c2)) // 2)   # ceil
    N_hi = (4*(a1 + lam)) // 5                                    # floor
    return N_lo, N_hi

def tier2(D, X4h, a1, a2, a3, c1, c2, bq1, Ffun):
    lam = a2 + a3 + 1 + X4h - bq1
    blocks_rest = a1 + 2*a2 + 2*a3 - bq1
    cost_sing = c1 + 7*c2 + 4*a3 + 2*bq1
    cost_rest = D - cost_sing
    sh, st = a2 + a3, max(0, a2 + a3 - bq1)
    if cost_rest < 0: return lam, blocks_rest, cost_rest, sh, st, None, True
    Fv = Ffun(lam, cost_rest, sh, st)
    return lam, blocks_rest, cost_rest, sh, st, Fv, blocks_rest > Fv

# ---------------------------------------------------------------- (i) algebra
print("== (i) the Tier-1 closed form is algebraically my Lemmas 4.9 + 4.10 ==")
# Lemma 4.10:  120 <= 5*n45 + 3*(a1-n45) + 4*a2 + 3*a3 + 4*c1 + 3*c2
#           => n45 >= (120 - 3a1 - 4a2 - 3a3 - 4c1 - 3c2)/2
# Lemma 4.9 :  n45 <= 4*R, R <= nS + lam = (a1 - n45) + lam
#           => 5*n45 <= 4*(a1 + lam)
bad = []
for (D, X4, e, X4h) in CLASSES16:
    for (a2, a3, c1, c2, a1, P) in censuses(D, X4, e, X4h):
        for bq1 in ((0, 1) if a2 + a3 >= 1 else (0,)):
            lam = a2 + a3 + 1 + X4h - bq1
            N_lo, N_hi = tier1(a1, a2, a3, c1, c2, lam)
            for n45 in range(a1 + 1):
                nS = a1 - n45
                budget_ok = 120 <= 5*n45 + 3*nS + 4*a2 + 3*a3 + 4*c1 + 3*c2
                cap_ok = n45 <= 4*(nS + lam)
                if (budget_ok and cap_ok) != (N_lo <= n45 <= N_hi):
                    bad.append((D, e, a2, a3, c1, c2, bq1, n45))
check("N_lo <= n45 <= N_hi is EXACTLY (Lemma 4.10 budget) and (Lemma 4.9 cap)",
      not bad, f"{len(bad)} mismatches")
print("      so a census with N_lo > N_hi has NO admissible n45: it is empty,")
print("      by two inequalities I proved necessary in coverage.md sect. 4.")
print("      b_q1=0 maximises lam hence N_hi, and N_lo is b_q1-free, so testing")
print("      at b_q1=0 is the WEAKEST test: DEAD there is DEAD for both.")

# ---------------------------------------------------------------- (ii)/(iii)/(iv)
def run(clause, Ffun, label):
    t1 = t2 = surv = 0
    rows2 = []
    for (D, X4, e, X4h) in CLASSES16:
        for (a2, a3, c1, c2, a1, P) in censuses(D, X4, e, X4h):
            if clause == 'c2' and c2 < 1: continue
            if clause == 'a3' and a3 < 1: continue
            lam0 = a2 + a3 + 1 + X4h            # b_q1 = 0: weakest
            N_lo, N_hi = tier1(a1, a2, a3, c1, c2, lam0)
            if N_lo > N_hi:
                t1 += 1; continue
            dead_all = True
            for bq1 in ((0, 1) if a2 + a3 >= 1 else (0,)):
                lam, br, cr, sh, st, Fv, dead = tier2(D, X4h, a1, a2, a3, c1,
                                                      c2, bq1, Ffun)
                rows2.append((D, X4, e, X4h, a2, a3, c1, c2, bq1, br, lam, cr,
                              sh, st, Fv, dead))
                if not dead: dead_all = False
            if dead_all: t2 += 1
            else: surv += 1
    print(f"  {label}: Tier-1 kills {t1}, Tier-2 kills {t2}, SURVIVORS {surv}"
          f"  (Tier-2 rows printed: {len(rows2)})")
    return t1, t2, surv, rows2

print("\n== (iii)/(iv) the two tiers, recomputed with my own F ==")
c1n, c2n, cs, crows = run('c2', F, "c2 >= 1")
check("c2 clause: 140 Tier-1 + 10 Tier-2 = 150 censuses, 0 survivors",
      (c1n, c2n, cs) == (140, 10, 0), f"{c1n}+{c2n}, surv={cs}")
check("c2 clause: 11 Tier-2 rows (the (20,0,0) e=4 census splits on b_q1)",
      len(crows) == 11, f"{len(crows)}")
a1n, a2n, as_, arows = run('a3', F, "a3 >= 1")
check("a3 clause: 148 Tier-1 + 2 Tier-2 = 150 censuses, 0 survivors",
      (a1n, a2n, as_) == (148, 2, 0), f"{a1n}+{a2n}, surv={as_}")

print("\n  Tier-2 table for c2 >= 1 (complete, 11 rows):")
print(f"  {'class':22s} {'a2 a3 c1 c2 bq1':16s} {'blk':>4s} {'lam':>4s} "
      f"{'cost':>5s} {'sh st':>6s} {'F':>4s}  verdict")
for r in crows:
    D, X4, e, X4h, a2, a3, c1, c2, bq1, br, lam, cr, sh, st, Fv, dead = r
    print(f"  ({D},{X4},0) e={e} X4h={X4h}      {a2}  {a3}  {c1}  {c2}   {bq1}   "
          f"{br:4d} {lam:4d} {cr:5d}  {sh}  {st}  {Fv:4d}  "
          f"{'DEAD' if dead else '*** ALIVE ***'}")
print("\n  Tier-2 table for a3 >= 1 (complete):")
for r in arows:
    D, X4, e, X4h, a2, a3, c1, c2, bq1, br, lam, cr, sh, st, Fv, dead = r
    print(f"  ({D},{X4},0) e={e} X4h={X4h}      {a2}  {a3}  {c1}  {c2}   {bq1}   "
          f"{br:4d} {lam:4d} {cr:5d}  {sh}  {st}  {Fv:4d}  "
          f"{'DEAD' if dead else '*** ALIVE ***'}")

# ---------------------------------------------------------------- (v) robustness
print("\n== (v) robustness: drop the un-re-derived table value g(20) = 25 ==")
from functools import lru_cache
def g_lin(c, a, b):
    if c < 0: return NEG
    if (a + b >= 1) and c == 0: return NEG
    if c <= 16: return g(c, a, b)
    return 4 - 2*a - 2*b + 2*c            # C6-B alone, strictly weaker
@lru_cache(maxsize=None)
def F_lin(k, c, sh, st):
    if k == 0: return 0 if (sh <= 0 and st <= 0 and c >= 0) else NEG
    if c < 0: return NEG
    best = NEG
    for ci in range(c + 1):
        for a in (0, 1):
            for b in (0, 1):
                v = g_lin(ci, a, b)
                if v == NEG: continue
                r = F_lin(k-1, c-ci, max(0, sh-a), max(0, st-b))
                if r != NEG and v + r > best: best = v + r
    return best
check("F_lin over-covers F on the whole consumed range",
      all(F_lin(k, c, s, t) >= F(k, c, s, t)
          for k in range(1, 8) for c in range(0, 26)
          for s in range(3) for t in range(3)))
b1, b2, bs, _ = run('c2', F_lin, "c2 >= 1 (cap-mode 'lin')")
d1, d2, ds, _ = run('a3', F_lin, "a3 >= 1 (cap-mode 'lin')")
check("both clauses still have 0 survivors without g(20)=25",
      bs == 0 and ds == 0, f"c2 surv={bs}, a3 surv={ds}")

# ---------------------------------------------------------------- (vi) discrimination
print("\n== (vi) discrimination: the same two tiers OUTSIDE the 871 budget ==")
alive = []
for (D, e) in [(25, 3), (25, 5), (25, 8), (25, 11), (25, 12), (30, 5)]:
    n = 0
    for (a2, a3, c1, c2, a1, P) in censuses(D, 0, e, 0):
        if c2 < 1: continue
        lam0 = a2 + a3 + 1
        N_lo, N_hi = tier1(a1, a2, a3, c1, c2, lam0)
        if N_lo > N_hi: continue
        for bq1 in ((0, 1) if a2 + a3 >= 1 else (0,)):
            *_, dead = tier2(D, 0, a1, a2, a3, c1, c2, bq1, F)
            if not dead: n += 1; break
    alive.append(((D, e), n))
    print(f"  ({D},0,0) e={e}: {n} censuses with c2 >= 1 SURVIVE both tiers")
check("the two tiers ADMIT type-II cycles outside the 871 budget",
      any(n > 0 for _, n in alive))
check("they admit NONE inside it (all 16 classes)", cs == 0 and as_ == 0)

# ---------------------------------------------------------------- consistency
print("\n== consistency with my own census (coverage.md sect. 7) ==")
tot = sum(len(configs_of_cell(*c)) for c in Z0_CLASSES)
allz = all(k[1] == 0 and k[3] == 0 for c in Z0_CLASSES for k in configs_of_cell(*c))
check("my Algorithm G still emits 200 configurations, all with a3 = c2 = 0",
      tot == 200 and allz, f"{tot}")

print(f"\n{'TIER DERIVATION INDEPENDENTLY VERIFIED' if fail == 0 else f'{fail} FAILURES'}")
sys.exit(1 if fail else 0)
