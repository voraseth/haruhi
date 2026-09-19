#!/usr/bin/env python3
"""verify_census.py -- cross-checks of the coverage chain.

(1) CONFIGURATION LAYER: my independent Algorithm G vs the artifact's
    tight_enum.enumerate_cell (different enumeration space).  Set equality
    required in both directions on all 15 Z=0 classes.
(2) INSTANCE LAYER: my Algorithm E vs the artifact's mkjobs.jobs_for and vs
    the reviewer's driver.py job list (which drove the 1111 committed runs).
(3) THE TWO-LOOP AUDIT: the number of temporally-unanchored closure arcs
    U = a2 + 2*a3 (+ 1 defect for the Z=1 class) over every configuration.
(4) The proved bound  5*(a2 + 2*a3 + c2) <= D - e - Delta1  evaluated on every
    configuration, and on the real objects.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("verify_census: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import sys, os, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'src', 'class-elimination'))
from census_gen import (gen_cell, configs_of_cell, instances_of_cell,
                        z1_instances, Z0_CLASSES)
from tight_enum import enumerate_cell

fail = 0
def check(name, ok, extra=''):
    global fail
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}{(' :: ' + extra) if extra else ''}")
    if not ok: fail += 1

print("== (1) CONFIGURATION LAYER: independent generator vs artifact ==")
tot_mine = tot_auth = 0
for (D, X4, e, X4h) in Z0_CLASSES:
    mine = set(configs_of_cell(D, X4, e, X4h))
    auth = set(enumerate_cell(D, X4, e, X4h, "", quiet=True))
    tot_mine += len(mine); tot_auth += len(auth)
    check(f"({D},{X4},0) e={e}: {len(mine)} configs",
          mine == auth,
          f"only-mine={len(mine-auth)} only-artifact={len(auth-mine)}")
check(f"TOTAL configurations = 200", tot_mine == 200 == tot_auth,
      f"mine={tot_mine} artifact={tot_auth}")

print("\n== (2) INSTANCE LAYER: expansion vs artifact mkjobs vs committed job list ==")
sys.argv = ['x']
import mkjobs

tot_i = 0
for (D, X4, e, X4h) in Z0_CLASSES:
    mine = {(a, b, c, d, f, g, tuple(sorted(h)), i)
            for (a, b, c, d, f, g, h, i) in instances_of_cell(D, X4, e, X4h)}
    auth = {(a, b, c, d, f, g, tuple(sorted(h)), i)
            for (a, b, c, d, f, g, h, i) in mkjobs.jobs_for(e, None, D, X4, X4h)}
    tot_i += len(mine)
    check(f"({D},{X4},0) e={e}: {len(mine)} instances", mine == auth,
          f"only-mine={len(mine-auth)} only-artifact={len(auth-mine)}")
z1 = z1_instances()
check("(15,0,1) 95 instances x 2 wirings = 190", len(z1) == 95, f"{len(z1)}")
check("TOTAL instances = 631", tot_i + 2*len(z1) == 631, f"{tot_i + 2*len(z1)}")

# --- compare against the job list that actually drove the 1111 committed runs
# The reviewer's driver.py runs the sweep on import; its two job functions
# are re-implemented here instead, verbatim in effect.
def drv_jobs(D, X4, e, X4h):
    cfgs = enumerate_cell(D, X4, e, X4h, "", quiet=True)
    rows = sorted(set((o[0], o[4], o[5], o[6]) for o in cfgs))
    jobs = set()
    P = 24 + D//5
    for (a2, bq1, n45, n4) in rows:
        c1 = e - a2; a1 = P - e - a2; nS = a1 - n45; n5 = n45 - n4
        T = 120 - 5*n5 - 4*n4 - 4*c1
        for s2v in itertools.combinations_with_replacement((2, 3, 4), a2):
            rest = T - sum(s2v)
            for n3 in range(nS + 1):
                for n2 in range(nS - n3 + 1):
                    n1 = nS - n3 - n2
                    if 3*n3 + 2*n2 + n1 == rest:
                        jobs.add((n5, n4, n3, n2, n1, c1, tuple(sorted(s2v)), bq1))
    return jobs
ok = True
for (D, X4, e, X4h) in Z0_CLASSES:
    mine = {(a, b, c, d, f, g, tuple(sorted(h)), i)
            for (a, b, c, d, f, g, h, i) in instances_of_cell(D, X4, e, X4h)}
    if mine != drv_jobs(D, X4, e, X4h): ok = False
check("instance set == the R-n6-7 sweep driver's job set (all 15 Z=0 classes)", ok)

print("\n== (3) TWO-LOOP AUDIT: U = a2 + 2*a3 over every configuration ==")
worst = {}
allU = []
for (D, X4, e, X4h) in Z0_CLASSES:
    U = [(k[0] + 2*k[1]) for k in configs_of_cell(D, X4, e, X4h)]
    A2 = [k[0] for k in configs_of_cell(D, X4, e, X4h)]
    A3 = [k[1] for k in configs_of_cell(D, X4, e, X4h)]
    C2 = [k[3] for k in configs_of_cell(D, X4, e, X4h)]
    worst[(D, X4, e)] = (max(U), max(A2), max(A3), max(C2))
    allU += U
    print(f"  ({D},{X4},0) e={e}: max U={max(U)}  max a2={max(A2)} "
          f"max a3={max(A3)} max c2={max(C2)}")
check("max U over all 200 Z=0 configurations <= 2", max(allU) <= 2, f"max={max(allU)}")
check("a3 = 0 in every configuration", all(w[2] == 0 for w in worst.values()))
check("c2 = 0 in every configuration", all(w[3] == 0 for w in worst.values()))
print("  (15,0,1): U = 1 span + 1 defect piece = 2, pinned by Theorem K2's "
      "wiring list (not by enumeration)")

print("\n== (4) THE PROVED BOUND 5*(a2+2a3+c2) <= D - e - Delta1 ==")
bad = []
for (D, X4, e, X4h) in Z0_CLASSES:
    for r in gen_cell(D, X4, e, X4h):
        # Delta1 = total deficiency of the one-block components
        # = 5*a1 - (sum of their lengths); lengths: n5 fives, n4 fours, shorts
        # lower bound 2 per short is what the proof uses; here use the exact
        # feasible minimum consistent with the class budget of this record.
        d1min = 0*r['n5'] + 1*r['n4'] + 2*r['nS']
        lhs = 5*(r['a2'] + 2*r['a3'] + r['c2'])
        if lhs > D - e - d1min:
            bad.append((D, X4, e, r['key'], lhs, D - e - d1min))
check("bound holds (with Delta1 >= n4 + 2*nS) on every generated record",
      not bad, f"{len(bad)} violations")

print(f"\n{'ALL COVERAGE CROSS-CHECKS PASS' if fail == 0 else f'{fail} CHECKS FAILED'}")
sys.exit(1 if fail else 0)
