#!/usr/bin/env python3
"""itemA independent scan: minimize t = extra+alpha+h subject to (i)-(vi)
at n=6, m=120+extra. Independent reimplementation of the Theorem-5 scan
(bounds/checks/certify_scan.py) from the constraint list alone.

Range sufficiency: extra, alpha, h >= 0 and t = extra+alpha+h, so any
profile with t <= T has extra,alpha,h <= T; e3 <= extra, Q2 <= e3,
Ncyc <= extra - Q2 are then bounded too. Scanning t <= 28 (> 24) is
therefore exhaustive for deciding min t (and we exhibit t=24 feasible).
dirty is scanned at its MAXIMUM d2 + e3//2 only: F enters (iv) as -(F-Ncyc)
on the RHS of a PT lower bound and (vi) as +F in a PT upper bound, so
raising dirty only enlarges the feasible region (a relaxation): valid for
a lower bound on t.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("itemA_scan6: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
T = 28
best = None; arg = None
for extra in range(T+1):
    m = 120 + extra
    for alpha in range(T+1-extra):
        for h in range(T+1-extra-alpha):
            t = extra + alpha + h
            if best is not None and t >= best: continue
            for e3 in range(extra+1):
                d2 = extra - e3
                dirty = d2 + e3 // 2          # maximal (relaxation)
                F = extra + dirty
                for Q2 in range(min(e3, extra)+1):        # (ii), part of (i)
                    for Ncyc in range(extra - Q2 + 1):    # (i)
                        Delta = 5*(1 + alpha + Q2 + Ncyc) - m
                        if Delta < 0: continue            # (iii)
                        lo = max(0, 1 + alpha + Q2 - Delta - (F - Ncyc))  # (iv)
                        hi = min(m // 5, (4*(2 + h + alpha + F)) // 5)    # (v),(vi)
                        if lo <= hi:
                            if best is None or t < best:
                                best, arg = t, (extra,e3,Q2,Ncyc,alpha,h,Delta,lo,hi)
print("min t =", best)
print("attained at (extra,e3,Q2,Ncyc,alpha,h,Delta,PTlo,PThi) =", arg)
if best != 24:
    import sys as _s; _s.exit(f"FAIL: min t = {best}, expected 24")
print("PASS: min t = 24, hence W >= 119+24 = 143 and L(6) >= 868")
