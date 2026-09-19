#!/usr/bin/env python3
"""frontier.py -- the certified hop-chain capacity data and the multi-chain
packing function F, written self-contained for the finlem treatments.

PROVENANCE OF THE TABLE (each row is a mathematical claim about hop-chains of
every first-occurrence ordering, not a heuristic):

  g(c,a,b) = max number of link-paths in a hop-chain of cost <= c whose first
             path is short if a=1 and whose last path is short if b=1.

Rows 0..16 are re-certified IN THIS WORKDIR by checks/chainpareto.c, a complete
DFS over the chain abstraction with no pruning other than the cost budget and
the class-disjointness that define the abstraction:
    logs/frontier_c15.log   nodes =   740,052,451   rows 0..15
    logs/frontier_c16.log   nodes = 2,034,132,013   rows 0..16
They agree entry-for-entry with the registered C6-C table (proof6.md sect. 7,
even rows) and with the T-n6-tight re-certification (proof_tight.md sect. 6).

Beyond cost 16 two upper bounds are available:
  (LIN)  C6-B: value := blocks - 2*cost <= 4 - 2a - 2b, i.e.
         g(c,a,b) <= 4 - 2a - 2b + 2c   for every c.   [proof6.md C6-B]
  (G20)  the registered g(20) = 25 plus monotonicity of g in c.
`cap(c,a,b,mode)` uses min(LIN,G20) in mode 'full' (= tight_enum.py's cap) and
LIN only in mode 'lin'.  Mode 'lin' is strictly weaker, hence strictly more
conservative; all three lemma scripts here are re-run in both modes and the
verdicts are identical, so NOTHING below depends on the unre-derived g(20)=25.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("frontier: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 1 `assert` statements")
from functools import lru_cache


INF = float('-inf')

# c: (free, short-first, short-last, both-short); None = unrealizable
GTAB = {
    0: (4, None, None, None), 1: (4, 4, 4, 1), 2: (7, 4, 4, 4),
    3: (7, 7, 7, 4), 4: (10, 7, 7, 7), 5: (10, 10, 10, 7),
    6: (11, 10, 10, 10), 7: (13, 11, 11, 10), 8: (14, 13, 13, 11),
    9: (15, 14, 14, 13), 10: (16, 15, 15, 14), 11: (17, 16, 16, 15),
    12: (19, 17, 17, 16), 13: (19, 19, 19, 17), 14: (22, 19, 19, 19),
    15: (22, 22, 22, 19), 16: (22, 22, 22, 22),
}

MODE = 'full'          # 'full' = min(g(20)=25, C6-B);  'lin' = C6-B only


def cap(c, a, b):
    """Upper bound on the number of link-paths of one hop-chain of cost <= c
    with endpoint shortness (a,b).  INF (= -inf) marks 'no such chain'."""
    if c < 0:
        return INF
    if a + b >= 1 and c == 0:
        return INF                      # a short endpoint path costs >= 1
    col = 0 if (a == 0 and b == 0) else (3 if (a == 1 and b == 1) else 1)
    if c <= 16:
        v = GTAB[c][col]
        return v if v is not None else 4
    lin = 4 - 2 * a - 2 * b + 2 * c     # C6-B
    if MODE == 'full' and c <= 20:
        return min(25, lin)             # registered g(20)=25 + monotonicity
    return lin


@lru_cache(maxsize=None)
def _F(k, m, sh, st, mode):
    """max total blocks over k hop-chains of total cost <= m, at least sh of
    which have a short first path and at least st a short last path."""
    if k == 0:
        return 0 if (sh <= 0 and st <= 0 and m >= 0) else INF
    if m < 0:
        return INF
    best = INF
    for c in range(m + 1):
        for a in (0, 1):
            for b in (0, 1):
                v = cap(c, a, b)
                if v == INF:
                    continue
                r = _F(k - 1, m - c, max(0, sh - a), max(0, st - b), mode)
                if r != INF and v + r > best:
                    best = v + r
    return best


def F(k, m, sh, st):
    return _F(k, m, sh, st, MODE)


def set_mode(mode):
    global MODE
    assert mode in ('full', 'lin')
    MODE = mode


if __name__ == '__main__':
    # self-check: the table as printed, and the F values quoted in finlem.md
    print("g(c,a,b), rows 0..16 (free / short-first / short-last / both-short)")
    for c in range(17):
        print(f"  {c:2d}  " + "  ".join(
            ('-' if GTAB[c][j] is None else str(GTAB[c][j])) for j in range(4)))
    print()
    quoted = [(2, 8, 0, 0, 20), (1, 13, 0, 0, 19), (2, 15, 2, 0, 25),
              (2, 15, 1, 1, 25), (2, 14, 1, 0, 25), (2, 12, 1, 0, 23),
              (3, 15, 2, 1, 30), (2, 13, 2, 0, 23), (2, 14, 0, 1, 25),
              (2, 12, 0, 1, 23), (3, 15, 1, 2, 30), (2, 13, 1, 1, 23),
              (2, 14, 1, 1, 24), (1, 14, 1, 0, 19), (1, 12, 0, 0, 19)]
    ok = True
    for k, m, sh, st, want in quoted:
        got = F(k, m, sh, st)
        flag = 'OK ' if got == want else '***MISMATCH***'
        ok &= (got == want)
        print(f"  F({k},{m},{sh},{st}) = {got:3d}  (quoted {want})  {flag}")
    print("F SELF-CHECK:", "PASS" if ok else "FAIL")
