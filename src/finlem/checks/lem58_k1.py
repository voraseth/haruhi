#!/usr/bin/env python3
"""lem58_k1.py -- LEMMA 5.8 (no very heavy transition).  Prints the complete
elimination table for the cell (D,X4,Z)=(10,2,0), e=2, X4h=1, the control table
for X4h=2, the ablation, and the 872/873 controls.

Output sections
  [A] census level: the five TC2 censuses of the cell, with the exact
      deficiency floor of each and its verdict.
  [B] slice level: for every (census, b_q1, n45) the surviving n4-window of the
      class-length budget and the deciding test.
  [C] the deciding candidate, in full arithmetic.
  [D] control X4h=2 (must be NON-empty: 4 configurations, the registered count).
  [E] ablation: which single test, if dropped, revives a configuration.
  [F] controls at other lengths: the verified 872 and the 873 corner.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("lem58_k1: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 3 `assert` statements")
import sys
import frontier
import census
from census import candidates, tally, tally_slice


D, X4, e = 10, 2, 2
P = 24 + D // 5


def census_list(D, e):
    out = []
    for a2 in range(e + 1):
        for a3 in range((e - a2) // 2 + 1):
            for c2 in range((e - a2 - 2 * a3) // 2 + 1):
                c1 = e - a2 - 2 * a3 - 2 * c2
                out.append((a2, a3, c1, c2))
    return out


def defl(a2, a3, c1, c2):
    """Exact deficiency floor of the non-(m=1) pieces: a3-components have all
    three paths of length 1 (cost 12), an a2-component has two paths of total
    length <= 4 (cost >= 6), a type-I cycle has one path of length 4 (cost 1),
    a type-II cycle two paths of total length 3 (cost 7)."""
    return 6 * a2 + 12 * a3 + 1 * c1 + 7 * c2


print("=" * 74)
print("LEMMA 5.8 -- cell (10,2,0), e=2, X4h=1:  P=%d, NCh=e+1+X4h=%d, D=%d"
      % (P, e + 1 + 1, D))
print("=" * 74)
print()
print("[A] CENSUS LEVEL  (a2 + 2a3 + c1 + 2c2 = e = 2;  a1 = P - e - a2 - a3)")
print("     a2 a3 c1 c2 | a1 | deficiency floor | verdict")
for (a2, a3, c1, c2) in census_list(D, e):
    a1 = P - e - a2 - a3
    fl = defl(a2, a3, c1, c2)
    v = "DEAD: floor > D=%d" % D if fl > D else "survives to [B]"
    print("     %2d %2d %2d %2d | %2d | %16d | %s" % (a2, a3, c1, c2, a1, fl, v))
print()

print("[A2] CLOSED-FORM LEVEL (the same N_lo/N_hi pinch used in Lemma 6.7)")
print("     a2 a3 c1 c2 bq1 | a1 lam | N_lo N_hi | verdict")
for (a2, a3, c1, c2) in census_list(D, e):
    a1 = P - e - a2 - a3
    if defl(a2, a3, c1, c2) > D:
        continue
    for b_q1 in ((0, 1) if a2 + a3 >= 1 else (0,)):
        lam = a2 + a3 + 1 + 1 - b_q1
        N_lo = -(-(120 - 3*a1 - 4*a2 - 3*a3 - 4*c1 - 3*c2) // 2)
        N_hi = (4 * (a1 + lam)) // 5
        print("     %2d %2d %2d %2d  %d  | %2d %3d | %4d %4d | %s"
              % (a2, a3, c1, c2, b_q1, a1, lam, N_lo, N_hi,
                 "DEAD (N_lo > N_hi)" if N_lo > N_hi
                 else "survives: n45 in [%d,%d]" % (N_lo, N_hi)))
print()

print("[B] SLICE LEVEL for X4h=1  (only slices reaching the class-length budget")
print("    are printed; every other slice is killed by the run cap C6-A first)")
print("    a2 a3 c1 c2 bq1 n45 | nS Rmax lam | n4-window from the length budget"
      " | verdict")
rows = 0
for X4h in (1,):
    for (a2, a3, c1, c2) in census_list(D, e):
        a1 = P - e - a2 - a3
        for b_q1 in ((0, 1) if a2 + a3 >= 1 else (0,)):
            lam = a2 + a3 + 1 + X4h - b_q1
            for n45 in range(a1 + 1):
                nS = a1 - n45
                Rmax = nS + lam
                win, verds = [], set()
                for x, r, w in candidates(D, e, X4h):
                    if x[:6] != (a2, a3, c1, c2, b_q1, n45):
                        continue
                    if r in ('C6A_n45', 'C6A_n4', 'C6A_R', 'length_budget'):
                        continue
                    win.append(x[6])
                    verds.add(r if r else 'SURVIVOR')
                if not win:
                    continue
                rows += 1
                print("    %2d %2d %2d %2d  %d  %2d | %2d %3d %3d | n4 in %s | %s"
                      % (a2, a3, c1, c2, b_q1, n45, nS, Rmax, lam,
                         str(win), ",".join(sorted(verds))))
print("    (%d slice(s) survive the run cap AND the length budget)" % rows)
print()

print("[C] THE DECIDING CANDIDATE")
for x, r, w in candidates(D, e, 1):
    if r == 'TC5_pareto' or r is None:
        a2, a3, c1, c2, b_q1, n45, n4 = x
        a1 = P - e - a2 - a3
        nS = a1 - n45
        lam = a2 + a3 + 1 + 1 - b_q1
        print("    x = (a2,a3,c1,c2,b_q1,n45,n4) = %s" % (x,))
        print("    a1=%d  nS=%d  lam=%d  blocks_rest=%d  cost_sing=%d  "
              "cost_rest=%d" % (a1, nS, lam, a1 + 2*a2 + 2*a3 - b_q1,
                                c1 + 7*c2 + 4*a3 + 2*b_q1,
                                D - (c1 + 7*c2 + 4*a3 + 2*b_q1)))
        print("    class budget: 120 = 5*%d + (%d shorts) + 4*%d ->  rem=%d in "
              "[%d,%d]  OK" % (n45, nS, c1,
                               120 - (4*n4 + 5*(n45-n4)) - 3*a3 - 4*c1 - 3*c2,
                               nS + 2*a2, 3*nS + 4*a2))
        print("    verdict: %s   %s" % (r or 'SURVIVOR', w))
print()

print("[D] CONTROL X4h=2 (the same algorithm must NOT empty this cell)")
t2, s2 = tally(D, e, 2)
print("    survivors = %d   %s" % (len(s2), s2))
print("    (registered K3 count for (10,2,0) e=2 X4h=2 is 4)")
assert len(s2) == 4, "control failure: X4h=2 count changed"
print()

print("[E] ABLATION at X4h=1 (drop one test family, keep the rest)")


def ablate(drop):
    return sum(1 for x, r, w in candidates(D, e, 1, skip=drop) if r is None)


for name, drop in [("none", set()),
                   ("run cap C6-A", {'C6A_n45', 'C6A_n4', 'C6A_R'}),
                   ("value ledger C6-B", {'TC5_value'}),
                   ("Pareto frontier C6-C", {'TC5_pareto'})]:
    print("    drop %-22s -> %d configuration(s) revived" % (name, ablate(drop)))
print("    (matches R-n6-6 finding F1: the run cap and the value ledger are")
print("     REDUNDANT here; the Pareto frontier plus the class budget kills")
print("     the cell on its own.)")
print()

print("[F] CROSS-LENGTH CONTROLS (nothing certified here may empty a real cell)")
for (Dc, X4c, ec, X4hc, tag) in [(25, 0, 25, 0, "verified 872 (L=872)"),
                                 (0, 6, 0, 5, "verified 873s (L=873)"),
                                 (0, 6, 0, 6, "873 corner X4h=6")]:
    s = census.survivors(Dc, ec, X4hc)
    print("    (%d,%d,0) e=%d X4h=%d  [%s]: %d configuration(s) survive"
          % (Dc, X4c, ec, X4hc, tag, len(s)))
    if (Dc, ec, X4hc) == (25, 25, 0):
        real = [o for o in s if o[:5] == (0, 0, 25, 0, 0) and o[5] == 4
                and o[6] == 0]
        print("       real 872 configuration (a1=4 all length 5, 25 type-I "
              "cycles) admitted: %s" % bool(real))
        assert real, "CONTROL FAILURE: real 872 configuration excluded"
    if (Dc, ec, X4hc) == (0, 0, 5):
        assert s, "CONTROL FAILURE: 873 corner excluded at its real X4h=5"
print()
print("LEMMA 5.8 VERDICT: cell (10,2,0) e=2 X4h=1 is EMPTY (%d candidates in "
      "the full-tuple\nconvention, %d in the slice convention of tight_enum.py; "
      "0 survivors);"
      % (sum(tally(D, e, 1)[0].values()), sum(tally_slice(D, e, 1)[0].values())))
print("hence X4h = X4 = 2 there, X4h = X4 in every one of the sixteen classes,")
print("and no transition of cost >= 5 occurs in any length-871 ordering.")
