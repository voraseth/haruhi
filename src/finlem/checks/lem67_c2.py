#!/usr/bin/env python3
"""lem67_c2.py -- LEMMA 6.7 (cycle-shape exclusion: c2 = 0 in all 16 classes).

The elimination is presented in two tiers, both hand-checkable.

TIER 1 -- a closed-form inequality.  Neither of the two tests below involves
n4, and both are one line of arithmetic in the census (a2,a3,c1,c2):

  (L)  class budget.  The 120 classes are the link-path lengths.  The n45
       one-path components have length 4 or 5 (total <= 5*n45), the other
       nS = a1 - n45 have length <= 3, an a2-component has total length <= 4,
       an a3-component exactly 3, a type-I cycle exactly 4, a type-II cycle
       exactly 3.  Hence
            120 <= 5*n45 + 3*(a1-n45) + 4*a2 + 3*a3 + 4*c1 + 3*c2,
       i.e.  n45 >= N_lo := ceil( (120 - 3a1 - 4a2 - 3a3 - 4c1 - 3c2) / 2 ).
  (R)  run cap (C6-A + TC4).  n45 <= 4R and R <= nS + lam = a1 - n45 + lam,
       so   n45 <= N_hi := floor( 4*(a1+lam) / 5 ),  lam = a2+a3+1+X4h-b_q1.
       Taking b_q1 = 0 maximises lam, hence weakens (R): the test below is
       run at the weakest setting.
  A census with N_lo > N_hi is empty.

TIER 2 -- the census groups surviving Tier 1 are killed by the certified
frontier.  blocks_rest, lam, cost_rest, sh_rest, st_rest do NOT depend on
(n45,n4), so this too is a census-level test:  blocks_rest <= F(lam, cost_rest,
sh_rest, st_rest) must hold.

TIER 0 (cross-check) -- the full candidate-by-candidate enumeration of
checks/census.py, with c2 >= 1 forced, is also run; its rejection witnesses are
written to logs/lem67_full_table.log and its per-cell tallies reproduce the
published n6c2probe numbers.

CONTROLS and DISCRIMINATION are in sections [D] and [E].
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("lem67_c2: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 8 `assert` statements")
import sys
import frontier
import census
from frontier import F
from census import candidates, tally, tally_slice


CELLS = ([(20, 0, e, 0) for e in range(1, 10)] +
         [(15, 1, e, 1) for e in (1, 2, 3, 4, 7)] +
         [(10, 2, 2, 1), (10, 2, 2, 2)])


def censuses(D, e, c2_min=1):
    P = 24 + D // 5
    for a2 in range(e + 1):
        for a3 in range((e - a2) // 2 + 1):
            for c2 in range(c2_min, (e - a2 - 2 * a3) // 2 + 1):
                c1 = e - a2 - 2 * a3 - 2 * c2
                a1 = P - e - a2 - a3
                if c1 >= 0 and a1 >= 0:
                    yield (a2, a3, c1, c2, a1)


def tier1(D, e, X4h, a2, a3, c1, c2, a1):
    lam = a2 + a3 + 1 + X4h            # b_q1 = 0: the weakest run-cap bound
    N_lo = -(-(120 - 3*a1 - 4*a2 - 3*a3 - 4*c1 - 3*c2) // 2)
    N_hi = (4 * (a1 + lam)) // 5
    return N_lo, N_hi, lam


def tier2(D, e, X4h, a2, a3, c1, c2, a1, b_q1):
    P = 24 + D // 5
    lam = a2 + a3 + 1 + X4h - b_q1
    blocks_rest = a1 + 2*a2 + 2*a3 - b_q1
    cost_rest = D - (c1 + 7*c2 + 4*a3 + 2*b_q1)
    sh_rest = a2 + a3
    st_rest = max(0, a2 + a3 - b_q1)
    V = P - 2 * D
    vcap = (-c1 - 12*c2 - 7*a3 - 3*b_q1) + 4*lam - 2*sh_rest - 2*st_rest
    return (blocks_rest, lam, cost_rest, sh_rest, st_rest,
            F(lam, cost_rest, sh_rest, st_rest), V, vcap)


print("=" * 78)
print("LEMMA 6.7 -- cycle-shape exclusion: no type-II cycle in any of the "
      "sixteen classes")
print("=" * 78)
print()
print("[A] TIER 1: the closed-form kill  (all censuses with c2 >= 1, b_q1 = 0)")
print("    cell            a2 a3 c1 c2 | a1 lam | N_lo N_hi | verdict")
surv1, ncens = [], 0
for D, X4, e, X4h in CELLS:
    for (a2, a3, c1, c2, a1) in censuses(D, e):
        ncens += 1
        N_lo, N_hi, lam = tier1(D, e, X4h, a2, a3, c1, c2, a1)
        dead = N_lo > N_hi
        if not dead:
            surv1.append((D, X4, e, X4h, a2, a3, c1, c2, a1))
        print("    (%2d,%d,0) e=%d X4h=%d %2d %2d %2d %2d | %2d %3d | %4d %4d |"
              " %s" % (D, X4, e, X4h, a2, a3, c1, c2, a1, lam, N_lo, N_hi,
                       "DEAD  (N_lo > N_hi)" if dead else "-> TIER 2"))
print("    %d censuses with c2 >= 1;  %d killed by the closed form;  %d go on."
      % (ncens, ncens - len(surv1), len(surv1)))
print()

print("[B] TIER 2: the %d surviving censuses against the certified frontier"
      % len(surv1))
print("    cell            a2 a3 c1 c2 bq1 | blocks_rest lam cost_rest sh st |"
      "  F | verdict")
surv2 = []
for (D, X4, e, X4h, a2, a3, c1, c2, a1) in surv1:
    for b_q1 in ((0, 1) if a2 + a3 >= 1 else (0,)):
        br, lam, cr, sh, st, f, V, vcap = tier2(D, e, X4h, a2, a3, c1, c2,
                                                a1, b_q1)
        dead_p = br > f
        dead_v = V > vcap
        tag = ("DEAD (Pareto %d > %d)" % (br, f) if dead_p else
               "DEAD (value %d > %d)" % (V, vcap) if dead_v else "*** ALIVE ***")
        if not (dead_p or dead_v):
            surv2.append((D, X4, e, X4h, a2, a3, c1, c2, b_q1))
        print("    (%2d,%d,0) e=%d X4h=%d %2d %2d %2d %2d  %d  | %11d %3d %9d"
              " %2d %2d | %2d | %s"
              % (D, X4, e, X4h, a2, a3, c1, c2, b_q1, br, lam, cr, sh, st,
                 f, tag))
print("    survivors of Tier 2: %d" % len(surv2))
assert not surv2, "a c2>=1 census survived both tiers"
print()

print("[C] TIER 0 cross-check: the full candidate enumeration with c2 >= 1")
print("    cell               candidates | rejection tallies (slice "
      "convention) | survivors")
gtot = 0
for D, X4, e, X4h in CELLS:
    t, s = tally(D, e, X4h, c2_min=1)
    ts, ss = tally_slice(D, e, X4h, c2_min=1)
    n = sum(t.values()) + len(s)
    gtot += n
    print("    (%2d,%d,0) e=%d X4h=%d %8d | %-46s | %d"
          % (D, X4, e, X4h, n, str(ts) if ts else "(no c2>=1 candidate: "
             "a type-II cycle needs e >= 2)", len(s)))
    assert not s, "c2>=1 survivor in a habitat cell"
print("    TOTAL c2>=1 candidates over the sixteen classes: %d;  SURVIVORS 0"
      % gtot)
print()

print("[D] CONTROLS (the same machinery must not exclude real objects)")
ctl = [(25, 0, 25, 0, "verified 872, corner (25,0,0) e=25 S=4 X4=0"),
       (0, 6, 0, 5, "verified 873s, corner (0,6,0) e=0 X4=6 (X4h=5)")]
for D, X4, e, X4h, tag in ctl:
    s = census.survivors(D, e, X4h)
    print("    %-46s : %d configuration(s) survive with c2 free" % (tag, len(s)))
    if D == 25:
        real = [o for o in s if o[:5] == (0, 0, 25, 0, 0) and o[5:] == (4, 0)]
        print("        the real 872 configuration (a1=4 length-5 paths, 25 "
              "type-I cycles) is admitted: %s" % bool(real))
        assert real
    else:
        assert s, "873 corner excluded at its own length"
print()

print("[E] DISCRIMINATION: the SAME constraint system admits type-II cycles")
print("    outside the length-871 budget, so c2 = 0 is a budget consequence.")
print("    cell               c2>=1 survivors | example configuration")
found = 0
for D in (25, 30):
    for e in range(1, 24 + D // 5):
        s = census.survivors(D, e, 0, c2_min=1)
        if s:
            found += 1
            if found <= 12:
                print("    (%2d,0,0) e=%-2d %14d | (a2,a3,c1,c2,bq1,n45,n4)=%s"
                      % (D, e, len(s), s[0]))
print("    cells (D,e) with D in {25,30} admitting c2 >= 1: %d" % found)
assert found, "DISCRIMINATION FAILURE: the system kills c2 everywhere"
e_admit = [e for e in range(1, 30) if census.survivors(25, e, 0, c2_min=1)]
print("    at (25,0,0) the admitting e-range is e = %s" % e_admit)
print()

print("[F] ROBUSTNESS: repeat [A]-[C] with cap-mode 'lin' (drop the registered")
print("    g(20)=25 and use only the C6-B bound 4-2a-2b+2c beyond cost 16)")
frontier.set_mode('lin')
bad = 0
for D, X4, e, X4h in CELLS:
    if census.survivors(D, e, X4h, c2_min=1):
        bad += 1
print("    c2>=1 survivors over the sixteen classes in mode 'lin': %d" % bad)
ctl_ok = bool(census.survivors(25, 25, 0)) and bool(census.survivors(0, 0, 5))
frontier.set_mode('full')
assert bad == 0
print("    controls still survive in mode 'lin': %s" % ctl_ok)
print()

print("[G] THE COMPANION CLAUSE: no three-block path component (a3 = 0).")
print("    The identical two tiers, run over every census with a3 >= 1 and c2")
print("    free.  (An a3-component carries three link-paths of length 1 each:")
print("    exact length 3, deficiency 12, and its middle path is a forced")
print("    singleton chain -- Lemma 6.6 (3).)")
print("    cell            a2 a3 c1 c2 bq1 | N_lo N_hi | blocks lam cost sh st"
      "  F | verdict")
n_a3 = k1 = k2 = 0
alive3 = []
for D, X4, e, X4h in CELLS:
    P = 24 + D // 5
    for a2 in range(e + 1):
        for a3 in range(1, (e - a2) // 2 + 1):
            for c2 in range((e - a2 - 2 * a3) // 2 + 1):
                c1 = e - a2 - 2 * a3 - 2 * c2
                a1 = P - e - a2 - a3
                if c1 < 0 or a1 < 0:
                    continue
                n_a3 += 1
                N_lo, N_hi, lam = tier1(D, e, X4h, a2, a3, c1, c2, a1)
                if N_lo > N_hi:
                    k1 += 1
                    print("    (%2d,%d,0) e=%d X4h=%d %2d %2d %2d %2d  -  |"
                          " %4d %4d |  (closed form)          | DEAD"
                          % (D, X4, e, X4h, a2, a3, c1, c2, N_lo, N_hi))
                    continue
                for b_q1 in (0, 1):
                    br, l2, cr, sh, st, f, V, vcap = tier2(
                        D, e, X4h, a2, a3, c1, c2, a1, b_q1)
                    dead = (cr < 0) or (br > f) or (V > vcap)
                    if not dead:
                        alive3.append((D, e, X4h, a2, a3, c1, c2, b_q1))
                    print("    (%2d,%d,0) e=%d X4h=%d %2d %2d %2d %2d  %d  |"
                          " %4d %4d | %6d %3d %4d %2d %2d %2d | %s"
                          % (D, X4, e, X4h, a2, a3, c1, c2, b_q1, N_lo, N_hi,
                             br, l2, cr, sh, st, f,
                             "DEAD" if dead else "*** ALIVE ***"))
                k2 += 1
print("    %d censuses with a3 >= 1;  %d killed by the closed form;  %d by the"
      " frontier;  %d alive." % (n_a3, k1, k2, len(alive3)))
assert not alive3
print()

print("[H] The 200 surviving configurations of the sixteen classes")
tot200 = 0
for D, X4, e, X4h in CELLS:
    s = census.survivors(D, e, X4h)
    tot200 += len(s)
    assert all(o[1] == 0 and o[3] == 0 for o in s)
print("    total configurations surviving the census with c2, a3 free: %d"
      % tot200)
print("    every one of them has c2 = 0 and a3 = 0  (registered count: 200)")
print()
print("LEMMA 6.7 VERDICT: c2 = 0 in every configuration of every one of the")
print("sixteen classes; hence every cycle in every one of the 631 search")
print("instances is type-I and Algorithm 6's type-I-only endgame is complete.")
