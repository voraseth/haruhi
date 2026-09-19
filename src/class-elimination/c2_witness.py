
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("c2_witness: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
#!/usr/bin/env python3
# c2_witness.py -- T-n6-c2 probe: for every c2>0 candidate configuration in
# every one of the 16 registered cells, record WHICH proved constraint of
# tight_enum.py rejects it.  Mirrors enumerate_cell exactly (diff-checked),
# but with c2 >= 1 forced and per-constraint rejection tallies.
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tight_enum import F


def probe_cell(D, X4, e, X4h):
    P = 24 + D // 5
    tallies = {}
    def rej(reason): tallies[reason] = tallies.get(reason, 0) + 1
    survivors = []
    for a2 in range(e + 1):
        for a3 in range((e - a2) // 2 + 1):
            for c2 in range(1, (e - a2 - 2*a3) // 2 + 1):   # c2 >= 1 FORCED
                c1 = e - a2 - 2*a3 - 2*c2
                a1 = P - e - a2 - a3
                if c1 < 0 or a1 < 0: rej('nonneg'); continue
                for b_q1 in ((0, 1) if a2 + a3 >= 1 else (0,)):
                    lam = a2 + a3 + 1 + X4h - b_q1
                    sh_rest = a2 + a3
                    st_rest = max(0, a2 + a3 - b_q1)
                    blocks_rest = a1 + 2*a2 + 2*a3 - b_q1
                    for n45 in range(a1 + 1):
                        nS = a1 - n45
                        Rmax = nS + lam
                        if n45 > 4 * Rmax: rej('C6A_n45'); continue
                        for n4 in range(n45 + 1):
                            if n4 > 2 * Rmax: rej('C6A_n4'); continue
                            if max((n45+3)//4, (n4+1)//2) > Rmax: rej('C6A_R'); continue
                            heavy = 4*n4 + 5*(n45 - n4)
                            sum_c1 = 4*c1; sum_c2 = 3*c2
                            rem = 120 - heavy - 3*a3 - sum_c1 - sum_c2
                            if not (nS + 2*a2 <= rem <= 3*nS + 4*a2): rej('length_budget'); continue
                            V = P - 2*D
                            v_sing = (2*sum_c1 - 9*c1) + (2*sum_c2 - 18*c2) - 7*a3 - 3*b_q1
                            if V > v_sing + 4*lam - 2*sh_rest - 2*st_rest: rej('TC5_value'); continue
                            cost_sing = (5*c1 - sum_c1) + (10*c2 - sum_c2) + 4*a3 + 2*b_q1
                            cost_rest = D - cost_sing
                            if cost_rest < 0: rej('TC5_cost_neg'); continue
                            if blocks_rest > F(lam, cost_rest, sh_rest, st_rest): rej('TC5_pareto'); continue
                            survivors.append((a2,a3,c1,c2,b_q1,n45,n4))
    return tallies, survivors

CELLS = ([(20,0,e,0) for e in range(1,10)] +
         [(15,1,e,1) for e in (1,2,3,4,7)] +
         [(10,2,2,1),(10,2,2,2)])
allok = True
for D,X4,e,X4h in CELLS:
    t, s = probe_cell(D,X4,e,X4h)
    print(f"({D},{X4},0) e={e} X4h={X4h}: c2>0 candidates rejected by {t}; SURVIVORS={len(s)}")
    if s:
        allok = False
        for o in s: print("   !! c2>0 SURVIVOR:", o)
print("VERDICT:", "c2=0 FORCED in every cell (no c2>0 candidate survives the proved constraints)" if allok else "*** c2>0 SURVIVES SOMEWHERE ***")
