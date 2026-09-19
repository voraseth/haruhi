#!/usr/bin/env python3
"""census_gen.py -- ALGORITHM G (the census generator) and ALGORITHM E (the
expansion), specified and implemented from scratch for T-n6-coverage.

Difference from src/class-elimination/tight_enum.py (the artifact's
generator): that one enumerates the COLLAPSED tuple (a2,a3,c1,c2,bq1,n45,n4)
and tests the short-length multiset only through an interval feasibility
window.  This implementation enumerates the FULL component length multiset
(n5,n4,n3,n2,n1 for one-block components, the exact s2 multiset for two-block
components, s3 = 3 for three-block ones) and then projects.  The two therefore
range over different search spaces; agreement of the projections is a genuine
cross-check, and the finer enumeration is what Algorithm E needs anyway.

Every rejection test is proved necessary in coverage.md sect. 3.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("census_gen: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import itertools, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pareto import F, NEG


# ---------------------------------------------------------------- helpers
def short_multisets(k, total):
    """all multisets of k values in {1,2,3} summing to `total`, as (n3,n2,n1)."""
    out = []
    for n3 in range(k + 1):
        for n2 in range(k - n3 + 1):
            n1 = k - n3 - n2
            if 3*n3 + 2*n2 + n1 == total:
                out.append((n3, n2, n1))
    return out

def s2_multisets(a2, total):
    """all multisets of a2 values in {2,3,4} summing to `total`, sorted desc."""
    out = []
    for n4 in range(a2 + 1):
        for n3 in range(a2 - n4 + 1):
            n2 = a2 - n4 - n3
            if 4*n4 + 3*n3 + 2*n2 == total:
                out.append(tuple([4]*n4 + [3]*n3 + [2]*n2))
    return out

# ---------------------------------------------------------------- ALGORITHM G
def gen_cell(D, X4, e, X4h, off=()):
    """Enumerate every admissible configuration of the Z=0 class (D,X4,0)/e/X4h.

    `off` names tests to DISABLE (ablation control): 'tc2c', 'runcap',
    'value', 'pareto', 'budget' (= G9, the class-length budget) and
    'costfeas' (= G11's cost-feasibility guard cost_rest >= 0, which the
    'pareto' switch alone leaves in force).  With off=() this is the
    full system.
    """
    P = 24 + D // 5                       # G1: P# = 24 + D/5
    res = []
    for a2 in range(e + 1):                                   # G2
        for a3 in range((e - a2)//2 + 1):                     # G2
            for c2 in range((e - a2 - 2*a3)//2 + 1):          # G2
                c1 = e - a2 - 2*a3 - 2*c2                     # G2 (identity)
                if c1 < 0: continue
                a1 = P - e - a2 - a3                          # G3 (identity)
                if a1 < 0: continue
                # G4: cycle closure TC2c -- exact class consumption
                if 'tc2c' in off:      # pre-TC2c: only the L2 five-vertex cap
                    c1rng = range(c1, 4*c1 + 1)
                else:
                    c1rng = (4*c1,)
                # G5: three-block components have sum l = 3 exactly
                sum_a3 = 3*a3
                for sum_c1 in c1rng:
                 for sum_c2 in (range(2*c2, 3*c2 + 1) if 'tc2c' in off else (3*c2,)):
                  for bq1 in ((0, 1) if a2 + a3 >= 1 else (0,)):        # G6
                      LAM = a2 + a3 + 1 + X4h - bq1                     # G7 (TC4)
                      sh_rest = a2 + a3
                      st_rest = max(0, a2 + a3 - bq1)
                      blocks_rest = a1 + 2*a2 + 2*a3 - bq1
                      for n5 in range(a1 + 1):
                       for n4 in range(a1 - n5 + 1):
                        nS = a1 - n5 - n4
                        n45 = n5 + n4
                        # G8: run caps C6-A  (R = #maximal {4,5}-runs)
                        Rmax = nS + LAM
                        if Rmax < 0: continue
                        if 'runcap' not in off:
                          if n45 > 4*Rmax or n4 > 2*Rmax: continue
                          if max(-(-n45//4), -(-n4//2)) > Rmax: continue
                        # G9: class budget -- the 120 classes are the path lengths
                        rem = 120 - 5*n5 - 4*n4 - sum_a3 - sum_c1 - sum_c2
                        # rem must split as (short lengths) + (s2 totals)
                        if 'budget' not in off:
                            if not (nS + 2*a2 <= rem <= 3*nS + 4*a2): continue
                        # G10: value ledger (C6-B with exact singleton values)
                        V = P - 2*D
                        v_sing = (2*sum_c1 - 9*c1) + (2*sum_c2 - 18*c2) - 7*a3 - 3*bq1
                        if 'value' not in off and V > v_sing + 4*LAM - 2*sh_rest - 2*st_rest: continue
                        # G11: Pareto ledger on the non-forced-singleton chains
                        cost_sing = (5*c1 - sum_c1) + (10*c2 - sum_c2) + 4*a3 + 2*bq1
                        cost_rest = D - cost_sing
                        if cost_rest < 0 and 'costfeas' not in off: continue
                        if 'pareto' not in off and blocks_rest > F(LAM, cost_rest, sh_rest, st_rest): continue
                        key = (a2, a3, c1, c2, bq1, n45, n4, sum_c1, sum_c2)
                        rec = dict(D=D, X4=X4, e=e, X4h=X4h, P=P, a1=a1, a2=a2,
                                   a3=a3, c1=c1, c2=c2, bq1=bq1, n5=n5, n4=n4,
                                   nS=nS, n45=n45, LAM=LAM, rem=rem, key=key)
                        res.append(rec)
    return res

def configs_of_cell(D, X4, e, X4h, off=()):
    """The paper's CONFIGURATION set of a class: distinct projected keys."""
    return sorted({r['key'] for r in gen_cell(D, X4, e, X4h, off)})

# ---------------------------------------------------------------- ALGORITHM E
def instances_of_cell(D, X4, e, X4h):
    """Expand every configuration into concrete piece multisets (INSTANCES).

    Instance key = (n5, n4, n3, n2, n1, c1, s2-multiset, bq1); the engine
    ranges internally over the (l1,l2) split of each span and over placements.
    """
    out = set()
    for r in gen_cell(D, X4, e, X4h):
        nS, a2, rem = r['nS'], r['a2'], r['rem']
        for s2v in s2_multisets(a2, 0) if a2 == 0 else \
                   [s for t in range(2*a2, 4*a2+1) for s in s2_multisets(a2, t)]:
            sigma = rem - sum(s2v)
            if sigma < 0: continue
            for (n3, n2, n1) in short_multisets(nS, sigma):
                out.add((r['n5'], r['n4'], n3, n2, n1, r['c1'], s2v, r['bq1']))
    return sorted(out)

# ---------------------------------------------------------------- the Z=1 class
def z1_instances():
    """The (15,0,1) defect class: two wirings (zh, zp3), each with the same
    length-parameter list (K2 of proof_tight.md pins the component skeleton:
    one two-block component A/B1 of total length sA in {2,3,4}, one defect
    piece B/B2 carrying a single path of length lB in {1..4}, 24 one-block
    components, no cycles).  Deficiency identity: the 24 singletons carry
    exactly sA + lB of deficiency."""
    out = set()
    for sA in (2, 3, 4):
        for lB in (1, 2, 3, 4):
            budget = sA + lB             # deficiency left for the 24 singletons
            for n4 in range(budget + 1):      # length-4 singletons, deficiency 1
                rest = budget - n4
                for n3 in range(rest//2 + 1):          # length 3, deficiency 2
                    for n2 in range((rest - 2*n3)//3 + 1):   # length 2, def 3
                        r = rest - 2*n3 - 3*n2
                        if r % 4: continue
                        n1 = r // 4                          # length 1, def 4
                        n5 = 24 - n4 - n3 - n2 - n1
                        if n5 < 0: continue
                        out.add((n5, n4, n3, n2, n1, sA, lB))
    return sorted(out)

# ---------------------------------------------------------------- the classes
Z0_CLASSES = ([(20, 0, e, 0) for e in range(1, 10)] +
              [(15, 1, e, 1) for e in (1, 2, 3, 4, 7)] +
              [(10, 2, 2, 2)])
