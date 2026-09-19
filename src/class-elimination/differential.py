
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("differential: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 2 `assert` statements")
#!/usr/bin/env python3
# differential.py -- certify that the probe's mirror of enumerate_cell is
# faithful: with min_c2=0 it must reproduce tight_enum.enumerate_cell's
# survivor set EXACTLY on all 16 registered cells + 6 control cells.
# Also: discrimination -- the same constraint system does NOT kill c2
# generically (c2>0 survives at (25,0,0) e=3..11 and broadly at D>=30),
# so the c2=0 forcing at L=871 is a budget consequence, not an artifact.
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tight_enum import enumerate_cell, F


def mirror(D, X4, e, X4h, min_c2=0):
    P = 24 + D // 5
    out = []
    for a2 in range(e + 1):
        for a3 in range((e - a2) // 2 + 1):
            for c2 in range(min_c2, (e - a2 - 2*a3) // 2 + 1):
                c1 = e - a2 - 2*a3 - 2*c2
                a1 = P - e - a2 - a3
                if c1 < 0 or a1 < 0: continue
                for b_q1 in ((0, 1) if a2 + a3 >= 1 else (0,)):
                    lam = a2 + a3 + 1 + X4h - b_q1
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
                            sum_c1, sum_c2 = 4*c1, 3*c2
                            rem = 120 - heavy - 3*a3 - sum_c1 - sum_c2
                            if not (nS + 2*a2 <= rem <= 3*nS + 4*a2): continue
                            V = P - 2*D
                            v_sing = (2*sum_c1 - 9*c1) + (2*sum_c2 - 18*c2) - 7*a3 - 3*b_q1
                            if V > v_sing + 4*lam - 2*sh_rest - 2*st_rest: continue
                            cost_sing = (5*c1 - sum_c1) + (10*c2 - sum_c2) + 4*a3 + 2*b_q1
                            cost_rest = D - cost_sing
                            if cost_rest < 0: continue
                            if blocks_rest > F(lam, cost_rest, sh_rest, st_rest): continue
                            out.append((a2, a3, c1, c2, b_q1, n45, n4, sum_c1, sum_c2))
    return out

if __name__ == '__main__':
    CELLS = ([(20,0,e,0) for e in range(1,10)] + [(15,1,e,1) for e in (1,2,3,4,7)] +
             [(10,2,2,1),(10,2,2,2)] + [(25,0,25,0)] + [(0,6,0,x) for x in (2,3,4,5,6)])
    ok = True
    for D,X4,e,X4h in CELLS:
        a = sorted(enumerate_cell(D,X4,e,X4h,"",quiet=True))
        b = sorted(mirror(D,X4,e,X4h,0))
        if a != b: ok = False; print(f"MISMATCH ({D},{X4},0) e={e} X4h={X4h}")
    print("DIFFERENTIAL:", "PASS" if ok else "FAIL")
    assert ok
    fat = [ (D,e) for D in (25,30) for e in range(1, 24+D//5)
            if mirror(D,0,e,0,min_c2=1) ]
    print("DISCRIMINATION: c2>0 survives at (D,e) in", fat[:8], "...", len(fat), "cells total -> the kill is NOT generic")
    assert fat
