#!/usr/bin/env python3
"""loopbound.py -- the TWO-LOOP BOUND, audited against a DELIBERATELY WEAKENED
constraint system.

coverage.md sect. 5 proves by hand that in every Z=0 class of the L=871 habitat

        U := a2 + 2*a3   <=  2                                        (*)

using ONLY: the component identities, the cycle-closure equalities (TC2c), the
deficiency identity D = 5*P# - 120, and the run caps C6-A (Lemma capacity(1))
via TC4.  It uses NEITHER the value ledger NOR the Pareto ledger.

This script re-derives (*) by brute force over the same weakened system, so the
bound does not depend on the (heavier) ledgers that the census generator also
applies.  If (*) held only because of the ledgers, this run would report U=3.

It also prints the per-e certificate of the hand proof's case analysis.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("loopbound: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import sys


CLASSES = ([(20, 0, e, 0) for e in range(1, 10)] +
           [(15, 1, e, 1) for e in (1, 2, 3, 4, 7)] +
           [(10, 2, 2, 2)])

def weak_admissible(D, X4, e, X4h, tc2c=True):
    """All (a2,a3,c1,c2,bq1,n5,n4,n3,n2,n1) admitted by the WEAK system."""
    P = 24 + D//5
    out = []
    for a2 in range(e + 1):
        for a3 in range((e - a2)//2 + 1):
            for c2 in range((e - a2 - 2*a3)//2 + 1):
                c1 = e - a2 - 2*a3 - 2*c2
                a1 = P - e - a2 - a3
                if c1 < 0 or a1 < 0: continue
                for bq1 in ((0, 1) if a2 + a3 >= 1 else (0,)):
                    LAM = a2 + a3 + 1 + X4h - bq1
                    if LAM < 0: continue
                    for n5 in range(a1 + 1):
                     for n4 in range(a1 - n5 + 1):
                      for n3 in range(a1 - n5 - n4 + 1):
                       for n2 in range(a1 - n5 - n4 - n3 + 1):
                        n1 = a1 - n5 - n4 - n3 - n2
                        nS = n3 + n2 + n1
                        n45 = n5 + n4
                        # run caps C6-A (TC4): R <= nS + LAM, n45 <= 4R, n4 <= 2R
                        R = nS + LAM
                        if n45 > 4*R or n4 > 2*R: continue
                        # deficiency identity, with the exact per-component
                        # minima: m=2 comps >= 6 (sum l <= 4), m=3 >= 12
                        # (sum l = 3), c1 cycles = 1, c2 cycles = 7 (TC2c)
                        Delta1 = 0*n5 + 1*n4 + 2*n3 + 3*n2 + 4*n1
                        lo = Delta1 + 6*a2 + 12*a3 + c1 + 7*c2
                        if lo > D: continue
                        # class budget: the 120 classes are exactly the path
                        # lengths; s2 in [2,4] per m=2 comp, s3 = 3, cycles fixed
                        base0 = 5*n5 + 4*n4 + 3*n3 + 2*n2 + 1*n1 + 3*a3
                        lo_c = (4*c1 + 3*c2) if tc2c else (1*c1 + 2*c2)
                        hi_c = (4*c1 + 3*c2)
                        if not (base0 + lo_c + 2*a2 <= 120 <= base0 + hi_c + 4*a2):
                            continue
                        out.append((a2, a3, c1, c2, bq1, n5, n4, n3, n2, n1))
    return out

fail = 0
print("== TWO-LOOP BOUND under the WEAK system (identities + TC2c + C6-A only) ==")
print("   (no value ledger, no Pareto ledger)")
gmax = 0
for (D, X4, e, X4h) in CLASSES:
    rec = weak_admissible(D, X4, e, X4h)
    U = max((r[0] + 2*r[1]) for r in rec) if rec else -1
    a2m = max((r[0] for r in rec), default=-1)
    a3m = max((r[1] for r in rec), default=-1)
    gmax = max(gmax, U)
    flag = '' if U <= 2 else '   *** EXCEEDS 2 ***'
    print(f"  ({D},{X4},0) e={e} X4h={X4h}: {len(rec):6d} weakly-admissible records, "
          f"max U={U} (max a2={a2m}, max a3={a3m}){flag}")
    if U > 2: fail += 1
print(f"  GLOBAL max U over all 15 Z=0 classes = {gmax}")
print(f"  [{'PASS' if gmax <= 2 else 'FAIL'}] U <= 2 under the weak system")
if gmax > 2: fail += 1

print("\n== the hand proof's case certificate (coverage.md sect. 5) ==")
print("   Step 1 (deficiency):  5*(a2+2a3+c2) <= D - e - Delta1")
for (D, X4, e, X4h) in CLASSES:
    b = (D - e) // 5
    print(f"  ({D},{X4},0) e={e}: 5*Lambda <= {D}-{e} = {D-e}  =>  Lambda <= {b}"
          + ("   (<=2 already)" if b <= 2 else "   (needs step 2)"))
print("   Step 2 (run cap) for the residual cases (20,0,0), e in {3,4,5}, U = 3:")
for e in (3, 4, 5):
    for (a2, a3) in ((3, 0), (1, 1)):
        P = 28
        D1max = 20 - e - 5*(a2 + 2*a3)      # Delta1 <= D - e - 5*Lambda
        a1 = P - e - a2 - a3
        nSmax = D1max // 2                  # each short comp costs >= 2
        LAM = a2 + a3 + 1 + 0               # X4h = 0, bq1 >= 0 taken best-case
        # need n45 = a1 - nS <= 4*(nS + LAM) for some nS <= nSmax
        need = None
        for nS in range(0, nSmax + 1):
            if a1 - nS <= 4*(nS + LAM):
                need = nS; break
        verdict = (f"satisfiable at nS={need}" if need is not None
                   else "IMPOSSIBLE (run cap violated for every nS)")
        ok = need is None
        if a2 > e: verdict = f"IMPOSSIBLE (a2={a2} > e={e})"; ok = True
        print(f"    e={e} (a2,a3)=({a2},{a3}): Delta1<={D1max}, a1={a1}, "
              f"nS<={nSmax}, LAM<={LAM}  ->  {verdict}")
        if not ok: fail += 1

print("\n== ROBUSTNESS: the same audit with TC2c's cycle-closure EQUALITY also off ==")
g2 = 0
for (D, X4, e, X4h) in CLASSES:
    rec = weak_admissible(D, X4, e, X4h, tc2c=False)
    U = max((r[0] + 2*r[1]) for r in rec) if rec else -1
    g2 = max(g2, U)
print(f"  max U with only the L2 five-vertex caps (no TC2c equality) = {g2}")
print(f"  [{'PASS' if g2 <= 2 else 'FAIL'}] U <= 2 without TC2c")
if g2 > 2: fail += 1

print(f"\n{'TWO-LOOP BOUND VERIFIED' if fail == 0 else f'{fail} FAILURES'}")
sys.exit(1 if fail else 0)
