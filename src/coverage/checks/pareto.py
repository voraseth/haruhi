#!/usr/bin/env python3
"""pareto.py -- the certified chain-capacity function F, re-implemented from the
statement of the capacity lemma (proof_tight.md sect. 6 / PAPER Appendix B).

F(k, c, sh, st) = the maximum number of link-paths ("blocks") that k chains of
TOTAL deficiency-cost c can carry, when sh of the chains are required to start
with a SHORT (<=3) path and st of them to end with a short path.

g(c,a,b) = per-chain maximum, taken from the registered/certified frontier
GTAB (rows 0..16, re-certified from scratch by n6tight/checks/chainpareto.c),
extended by the certified g(20)=25 and the C6-B fallback 4 - 2a - 2b + 2c.

This file is written from the LEMMA STATEMENT, not copied from tight_enum.py;
the GTAB numbers are the certified table itself (data, not code) and are
identical by construction -- that is the point of a certified table.
"""
from functools import lru_cache

NEG = float('-inf')

# c -> (free, short-first, short-last, short-both)
GTAB = {
 0:(4,None,None,None), 1:(4,4,4,1), 2:(7,4,4,4), 3:(7,7,7,4), 4:(10,7,7,7),
 5:(10,10,10,7), 6:(11,10,10,10), 7:(13,11,11,10), 8:(14,13,13,11),
 9:(15,14,14,13), 10:(16,15,15,14), 11:(17,16,16,15), 12:(19,17,17,16),
 13:(19,19,19,17), 14:(22,19,19,19), 15:(22,22,22,19), 16:(22,22,22,22)}

def g(c, a, b):
    """max blocks in ONE chain of cost c with short-first flag a, short-last b."""
    if c < 0:
        return NEG
    if (a + b >= 1) and c == 0:
        return NEG                      # a short endpoint costs deficiency >= 1
    col = 0 if (a == 0 and b == 0) else (3 if (a == 1 and b == 1) else 1)
    if c <= 16:
        v = GTAB[c][col]
        return 4 if v is None else v
    if c <= 20:
        return min(25, 4 - 2*a - 2*b + 2*c)     # certified g(20) = 25
    return 4 - 2*a - 2*b + 2*c                  # C6-B fallback

@lru_cache(maxsize=None)
def F(k, c, sh, st):
    """max total blocks over k chains of total cost c, sh short-heads, st short-tails."""
    if k == 0:
        return 0 if (sh <= 0 and st <= 0 and c >= 0) else NEG
    if c < 0:
        return NEG
    best = NEG
    for ci in range(c + 1):
        for a in (0, 1):
            for b in (0, 1):
                v = g(ci, a, b)
                if v == NEG:
                    continue
                r = F(k-1, c-ci, max(0, sh-a), max(0, st-b))
                if r != NEG and v + r > best:
                    best = v + r
    return best
