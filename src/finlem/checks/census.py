#!/usr/bin/env python3
"""census.py -- ALGORITHM A (the configuration census) written as a specified,
witness-producing procedure, for the Z=0 cells of the L=871 habitat.

A *configuration* of a hypothetical length-871 ordering in the cell
(D, X4, Z=0), e, X4h is the tuple

      x = (a2, a3, c1, c2, b_q1, n45, n4)

where (proof_tight.md sects. 3-5; PAPER-n6-872.tex Lemmas 6.2-6.4)
  a_m  = # pointer-graph PATH components carrying m link-paths (m = 1,2,3)
  c_m  = # pointer-graph CYCLE components carrying m link-paths (m = 1,2)
  b_q1 = 1 iff q_1's component carries m >= 2 link-paths
  n45  = # of the a1 one-path path components whose link-path has length 4 or 5
  n4   = # of those whose link-path has length exactly 4.
a1 and c1 are not free: a1 = P - e - a2 - a3 and c1 = e - a2 - 2a3 - 2c2.

DERIVED QUANTITIES (all exact identities, see finlem.md sect. 1.2):
  P            = 24 + D/5                          number of link-paths
  NCh          = e + 1 + X4h                       number of hop-chains
  #forced singleton chains = (c1 + 2 c2) + a3 + b_q1
  lam          = NCh - #forced singletons = a2 + a3 + 1 + X4h - b_q1
  blocks_rest  = P - #forced singletons = a1 + 2 a2 + 2 a3 - b_q1
  sh_rest      = a2 + a3                (rest-chains forced to start short)
  st_rest      = a2 + a3 - b_q1         (rest-chains forced to end short)
  nS           = a1 - n45               one-path components of length <= 3

REJECTION TESTS, in the fixed order in which the witness is recorded.  Each is
a proved necessary condition; the licensing proof is in finlem.md sect. 1.3.
  T0 nonneg        c1 >= 0, a1 >= 0
  T1 C6A_n45       n45 <= 4 * Rmax,  Rmax := nS + lam        [C6-A + TC4]
  T2 C6A_n4        n4  <= 2 * Rmax                            [C6-A + TC4]
  T3 C6A_R         max(ceil(n45/4), ceil(n4/2)) <= Rmax       [C6-A + TC4]
  T4 length_budget nS + 2 a2 <= rem <= 3 nS + 4 a2,           [class budget]
                   rem := 120 - (4 n4 + 5 (n45-n4)) - 3 a3 - 4 c1 - 3 c2
  T5 TC5_value     P - 2D <= v_sing + 4 lam - 2 sh_rest - 2 st_rest  [C6-B]
  T6 TC5_cost_neg  cost_rest := D - cost_sing >= 0
  T7 TC5_pareto    blocks_rest <= F(lam, cost_rest, sh_rest, st_rest) [C6-C]
with
  v_sing    = (2*4c1 - 9 c1) + (2*3c2 - 18 c2) - 7 a3 - 3 b_q1
  cost_sing = (5 c1 - 4 c1) + (10 c2 - 3 c2) + 4 a3 + 2 b_q1.

This is a faithful, documented restatement of src/class-elimination/
tight_enum.py::enumerate_cell; checks/diffcheck.py certifies survivor-set
equality against that generator on all 16 habitat cells and 6 control cells.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("census: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import math
from frontier import F


REASONS = ['nonneg', 'C6A_n45', 'C6A_n4', 'C6A_R', 'length_budget',
           'TC5_value', 'TC5_cost_neg', 'TC5_pareto']


def candidates(D, e, X4h, c2_min=0, skip=()):
    """Enumerate every configuration tuple of the cell.  Yields
    (x, reason, witness) with reason None for survivors.  `skip` names
    rejection tests to DISABLE (ablation): a candidate failing a skipped test
    is carried on to the remaining tests rather than being rejected."""
    skip = set(skip)
    P = 24 + D // 5
    for a2 in range(e + 1):
        for a3 in range((e - a2) // 2 + 1):
            for c2 in range(c2_min, (e - a2 - 2 * a3) // 2 + 1):
                c1 = e - a2 - 2 * a3 - 2 * c2
                a1 = P - e - a2 - a3
                if c1 < 0 or a1 < 0:
                    yield ((a2, a3, c1, c2, 0, -1, -1), 'nonneg',
                           f"c1={c1} a1={a1}")
                    continue
                for b_q1 in ((0, 1) if a2 + a3 >= 1 else (0,)):
                    lam = a2 + a3 + 1 + X4h - b_q1
                    sh_rest = a2 + a3
                    st_rest = max(0, a2 + a3 - b_q1)
                    blocks_rest = a1 + 2 * a2 + 2 * a3 - b_q1
                    V = P - 2 * D
                    v_sing = (8 * c1 - 9 * c1) + (6 * c2 - 18 * c2) \
                        - 7 * a3 - 3 * b_q1
                    cost_sing = c1 + 7 * c2 + 4 * a3 + 2 * b_q1
                    cost_rest = D - cost_sing
                    for n45 in range(a1 + 1):
                        nS = a1 - n45
                        Rmax = nS + lam
                        base = (a2, a3, c1, c2, b_q1, n45)
                        if n45 > 4 * Rmax and 'C6A_n45' not in skip:
                            for n4 in range(n45 + 1):
                                yield (base + (n4,), 'C6A_n45',
                                       f"n45={n45} > 4*Rmax={4*Rmax}")
                            continue
                        for n4 in range(n45 + 1):
                            x = base + (n4,)
                            if n4 > 2 * Rmax and 'C6A_n4' not in skip:
                                yield (x, 'C6A_n4',
                                       f"n4={n4} > 2*Rmax={2*Rmax}")
                                continue
                            Rneed = max(-(-n45 // 4), -(-n4 // 2))
                            if Rneed > Rmax and 'C6A_R' not in skip:
                                yield (x, 'C6A_R',
                                       f"R>={Rneed} > Rmax={Rmax}")
                                continue
                            heavy = 4 * n4 + 5 * (n45 - n4)
                            rem = 120 - heavy - 3 * a3 - 4 * c1 - 3 * c2
                            lo, hi = nS + 2 * a2, 3 * nS + 4 * a2
                            if not (lo <= rem <= hi) and 'length_budget' not in skip:
                                yield (x, 'length_budget',
                                       f"rem={rem} not in [{lo},{hi}]")
                                continue
                            vcap = v_sing + 4 * lam - 2 * sh_rest - 2 * st_rest
                            if V > vcap and 'TC5_value' not in skip:
                                yield (x, 'TC5_value',
                                       f"V={V} > {vcap}")
                                continue
                            if cost_rest < 0:
                                yield (x, 'TC5_cost_neg',
                                       f"cost_rest={cost_rest}")
                                continue
                            f = F(lam, cost_rest, sh_rest, st_rest)
                            if blocks_rest > f and 'TC5_pareto' not in skip:
                                yield (x, 'TC5_pareto',
                                       f"blocks_rest={blocks_rest} > "
                                       f"F({lam},{cost_rest},{sh_rest},"
                                       f"{st_rest})={f}")
                                continue
                            yield (x, None, "")


def survivors(D, e, X4h, c2_min=0):
    return [x for x, r, _ in candidates(D, e, X4h, c2_min) if r is None]


def tally(D, e, X4h, c2_min=0):
    t = {}
    surv = []
    for x, r, w in candidates(D, e, X4h, c2_min):
        if r is None:
            surv.append(x)
        else:
            t[r] = t.get(r, 0) + 1
    return t, surv


def tally_slice(D, e, X4h, c2_min=0):
    """The tally with the SLICE convention of tight_enum.py: when the test
    T1 (C6A_n45) fires it kills the whole n4-slice of that n45 in one count.
    Reproduces the counts published in PAPER-n6-872.tex / n6c2probe."""
    P = 24 + D // 5
    t, surv = {}, []
    def rej(r): t[r] = t.get(r, 0) + 1
    for a2 in range(e + 1):
        for a3 in range((e - a2) // 2 + 1):
            for c2 in range(c2_min, (e - a2 - 2 * a3) // 2 + 1):
                c1 = e - a2 - 2 * a3 - 2 * c2
                a1 = P - e - a2 - a3
                if c1 < 0 or a1 < 0:
                    rej('nonneg'); continue
                for b_q1 in ((0, 1) if a2 + a3 >= 1 else (0,)):
                    lam = a2 + a3 + 1 + X4h - b_q1
                    sh_rest, st_rest = a2 + a3, max(0, a2 + a3 - b_q1)
                    blocks_rest = a1 + 2 * a2 + 2 * a3 - b_q1
                    V = P - 2 * D
                    v_sing = -c1 - 12 * c2 - 7 * a3 - 3 * b_q1
                    cost_rest = D - (c1 + 7 * c2 + 4 * a3 + 2 * b_q1)
                    for n45 in range(a1 + 1):
                        nS = a1 - n45
                        Rmax = nS + lam
                        if n45 > 4 * Rmax:
                            rej('C6A_n45'); continue
                        for n4 in range(n45 + 1):
                            if n4 > 2 * Rmax:
                                rej('C6A_n4'); continue
                            if max(-(-n45 // 4), -(-n4 // 2)) > Rmax:
                                rej('C6A_R'); continue
                            heavy = 4 * n4 + 5 * (n45 - n4)
                            rem = 120 - heavy - 3 * a3 - 4 * c1 - 3 * c2
                            if not (nS + 2 * a2 <= rem <= 3 * nS + 4 * a2):
                                rej('length_budget'); continue
                            if V > v_sing + 4*lam - 2*sh_rest - 2*st_rest:
                                rej('TC5_value'); continue
                            if cost_rest < 0:
                                rej('TC5_cost_neg'); continue
                            if blocks_rest > F(lam, cost_rest, sh_rest, st_rest):
                                rej('TC5_pareto'); continue
                            surv.append((a2,a3,c1,c2,b_q1,n45,n4))
    return t, surv
