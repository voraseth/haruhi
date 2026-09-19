
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("tight_enum: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 3 `assert` statements")
#!/usr/bin/env python3
# tight_enum.py -- T-n6-tight refined cell enumeration for the Z=0 cells of the
# registered L=871 habitat (N871-B), under the tightness system of proof_tight.md:
#   TC1 exact chain count       NCh = e + 1 + X4h
#   TC2 tight component law     path comps k=m-1 (m<=3, sum l <= 6-m),
#                               cycles k=m (m<=2, sum l <= 5-m), nc-blocks singletons
#   TC3 forced singleton chains cycle paths, interior paths, q1-in-multi
#   TC4 separator lemma         chain-interior paths are singleton components;
#                               {4,5}-paths live only in singleton comps (or c1 l=4)
#   TC5 value/Pareto ledger     exact singleton values + C6-B/C6-C caps on the rest
# Every constraint is a PROVED necessary condition; the enumeration over-covers
# each cell, so a cell with zero surviving configurations is EMPTY.
# Controls: the verified 872's cell must survive AND admit the real 872's shape.
from functools import lru_cache


INF = float('-inf')
# Chain Pareto g(c,a,b), running max in c.
# Rows 0..15: re-certified from scratch by checks/chainpareto.c (this agent's own
# complete enumeration, logs/chainpareto15.log; even rows agree entry-for-entry
# with the registered C6-C table of proof6.md sect.7 -- the regression).
# Row 16: registered C6-C (22,22,22,22).  17..20: certified g(20)=25 fallback.
GTAB = {  # c: (free, sf, sl, ss)
 0:(4,None,None,None), 1:(4,4,4,1), 2:(7,4,4,4), 3:(7,7,7,4), 4:(10,7,7,7),
 5:(10,10,10,7), 6:(11,10,10,10), 7:(13,11,11,10), 8:(14,13,13,11),
 9:(15,14,14,13), 10:(16,15,15,14), 11:(17,16,16,15), 12:(19,17,17,16),
 13:(19,19,19,17), 14:(22,19,19,19), 15:(22,22,22,19), 16:(22,22,22,22)}
def cap(c, a, b):
    if c < 0: return INF
    if a + b >= 1 and c == 0: return INF        # a short endpoint costs >= 1
    col = 0 if (a==0 and b==0) else (3 if (a==1 and b==1) else 1)
    if c <= 16:
        v = GTAB[c][col]
        return v if v is not None else 4
    if c <= 20: return min(25, 4 - 2*a - 2*b + 2*c)   # certified g(20)=25
    return 4 - 2*a - 2*b + 2*c                        # C6-B fallback

@lru_cache(maxsize=None)
def F(k, m, sh, st):
    if k == 0: return 0 if (sh <= 0 and st <= 0 and m >= 0) else INF
    if m < 0: return INF
    best = INF
    for c in range(m + 1):
        for a in (0, 1):
            for b in (0, 1):
                v = cap(c, a, b)
                if v == INF: continue
                r = F(k-1, m-c, max(0, sh-a), max(0, st-b))
                if r != INF and v + r > best: best = v + r
    return best

def enumerate_cell(D, X4, e, X4h, tag, quiet=False):
    P = 24 + D // 5
    NCh = e + 1 + X4h
    out = []
    for a2 in range(e + 1):
        for a3 in range((e - a2) // 2 + 1):
            for c2 in range((e - a2 - 2*a3) // 2 + 1):
                c1 = e - a2 - 2*a3 - 2*c2
                a1 = P - e - a2 - a3
                if c1 < 0 or a1 < 0: continue
                for b_q1 in ((0, 1) if a2 + a3 >= 1 else (0,)):
                    lam = a2 + a3 + 1 + X4h - b_q1     # chains hosting a1 mids
                    sh_rest = a2 + a3
                    st_rest = max(0, a2 + a3 - b_q1)
                    blocks_rest = a1 + 2*a2 + 2*a3 - b_q1
                    for n45 in range(a1 + 1):
                        nS = a1 - n45
                        Rmax = nS + lam
                        if n45 > 4 * Rmax: continue
                        for n4 in range(n45 + 1):
                            if n4 > 2 * Rmax: continue
                            if max((n45+3)//4, (n4+1)//2) > Rmax: continue
                            heavy = 4*n4 + 5*(n45 - n4)
                            # CYCLE CLOSURE (TC2c): a pointer cycle closes only
                            # after 5 rho-steps (rho has order exactly 5 on all
                            # 720 perms, certified blockcheck), so every cycle
                            # has EXACTLY 5 vertices: m=1 -> l=4, m=2 -> l1+l2=3.
                            for sum_c1 in (4*c1,):
                                for sum_c2 in (3*c2,):
                                    # remaining length budget for short-a1 + a2 comps
                                    rem = 120 - heavy - 3*a3 - sum_c1 - sum_c2
                                    if not (nS + 2*a2 <= rem <= 3*nS + 4*a2): continue
                                    # TC5 value ledger (exact singleton values)
                                    V = P - 2*D
                                    v_sing = (2*sum_c1 - 9*c1) + (2*sum_c2 - 18*c2) - 7*a3 - 3*b_q1
                                    if V > v_sing + 4*lam - 2*sh_rest - 2*st_rest: continue
                                    # TC5 Pareto ledger on rest chains
                                    cost_sing = (5*c1 - sum_c1) + (10*c2 - sum_c2) + 4*a3 + 2*b_q1
                                    cost_rest = D - cost_sing
                                    if cost_rest < 0: continue
                                    if blocks_rest > F(lam, cost_rest, sh_rest, st_rest): continue
                                    out.append((a2, a3, c1, c2, b_q1, n45, n4, sum_c1, sum_c2))
    if not quiet:
        keys = {(c1+c2, n4, o[5]) for o in out for c1, c2, n4 in [(o[2], o[3], o[6])]}
        print(f"{tag}: (D,X4,Z)=({D},{X4},0) e={e} X4h={X4h} NCh={NCh}  "
              f"configs={len(out)}" + ("   *** EMPTY ***" if not out else ""))
    return out

if __name__ == '__main__':
    print("== CONTROLS (must survive) ==")
    s = enumerate_cell(25, 0, 25, 0, "CTRL L=872 (25,0,0) e=25")
    assert s, "CONTROL FAILURE: the verified 872's cell was excluded"
    real = [o for o in s if o[:5] == (0,0,25,0,0) and o[5] == 4 and o[6] == 0
            and o[7] == 100]
    assert real, "CONTROL FAILURE: the real 872 configuration is not admitted"
    ok873 = {}
    for X4h in (2,3,4,5,6):
        s3 = enumerate_cell(0, 6, 0, X4h, f"CTRL L=873 (0,6,0) e=0 X4h={X4h}")
        ok873[X4h] = bool(s3)
    assert ok873[5], "CONTROL FAILURE: the 873 corner excluded at its real X4h=5"
    print()
    print("== THE 13 Z=0 HABITAT CELLS AT L=871 ==")
    res = {}
    for e in range(1, 10):
        res[('20',e,0)] = enumerate_cell(20, 0, e, 0, f"(20,0,0) e={e}")
    for e in (1,2,3,4,7):
        res[('15',e,1)] = enumerate_cell(15, 1, e, 1, f"(15,1,0) e={e}")
    for X4h in (1,2):
        res[('10',2,X4h)] = enumerate_cell(10, 2, 2, X4h, f"(10,2,0) e=2 X4h={X4h}")
    print()
    empt = [k for k, v in res.items() if not v]
    print(f"EMPTY cells under the tightness system: {empt if empt else 'none'}")
