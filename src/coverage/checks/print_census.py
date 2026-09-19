#!/usr/bin/env python3
"""print_census.py -- the machine-regenerable census/instance table.

One command:  python3 checks/print_census.py > logs/census_table.txt
Prints (a) the 200 surviving configurations of the fifteen Z=0 classes, grouped
by class, and (b) their expansion into the 631 search instances (441 Z=0 +
2 x 95 for the Z=1 defect class), each tagged with the mode(s) run.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("print_census: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 1 `assert` statements")
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from census_gen import (gen_cell, configs_of_cell, instances_of_cell,
                        z1_instances, Z0_CLASSES)


def cname(D, X4, e, X4h):
    return f"({D},{X4},0)/e={e}/X4h={X4h}"

print("# CENSUS TABLE for the L=871 habitat N871-B")
print("# Regenerate:  python3 src/coverage/checks/print_census.py")
print("# Part A: the 200 configurations of the 15 Z=0 structural classes.")
print("# columns: a2 a3 c1 c2 bq1 | a1 n45 n4 nS | sumc1 sumc2 | LAM  (U = a2+2a3)")
print()
TOT = 0
for (D, X4, e, X4h) in Z0_CLASSES:
    recs = {}
    for r in gen_cell(D, X4, e, X4h):
        recs.setdefault(r['key'], r)
    keys = sorted(recs)
    TOT += len(keys)
    print(f"## CLASS {cname(D,X4,e,X4h)}   P#={24+D//5}  NCh={e+1+X4h}  "
          f"configurations={len(keys)}")
    for k in keys:
        r = recs[k]
        print(f"   a2={k[0]} a3={k[1]} c1={k[2]} c2={k[3]} bq1={k[4]} | "
              f"a1={r['a1']:2d} n45={k[5]:2d} n4={k[6]} nS={r['nS']:2d} | "
              f"sumc1={k[7]:3d} sumc2={k[8]} | LAM={r['LAM']} U={k[0]+2*k[1]}")
    print()
print(f"# Part A total: {TOT} configurations")
print()
print("# Part B: expansion into search instances.")
print("# Z=0 instance = (n5,n4,n3,n2,n1 | c1 | s2-multiset | bq1); the engine")
print("# ranges internally over each span's (l1,l2) split and over placements.")
print("# modes: m0 = linear closure; m1 = loop-complete (run iff the instance")
print("#        carries a loop-capable piece, i.e. s2-multiset non-empty).")
print()
NI = M0 = M1 = 0
for (D, X4, e, X4h) in Z0_CLASSES:
    inst = instances_of_cell(D, X4, e, X4h)
    NI += len(inst)
    ne = sum(1 for j in inst if len(j[6]) > 0)
    M0 += len(inst); M1 += ne
    print(f"## CLASS {cname(D,X4,e,X4h)}   instances={len(inst)}  "
          f"loop-exposed={ne}  (runs: {len(inst)} m0 + {ne} m1)")
    for (n5, n4, n3, n2, n1, c1, s2v, bq1) in inst:
        s = ','.join(map(str, s2v)) if s2v else '-'
        print(f"   n5={n5:2d} n4={n4} S=({n3}x3,{n2}x2,{n1}x1) c1={c1:2d} "
              f"s2=[{s}] bq1={bq1}  {'m0+m1' if s2v else 'm0'}")
    print()
z1 = z1_instances()
for wiring in ('zh', 'zp3'):
    print(f"## CLASS (15,0,1)/e=2 wiring={wiring}   instances={len(z1)}  "
          f"loop-exposed={len(z1)}  (runs: {len(z1)} m0 + {len(z1)} m1)")
    for (n5, n4, n3, n2, n1, sA, lB) in z1:
        print(f"   n5={n5:2d} n4={n4} S=({n3}x3,{n2}x2,{n1}x1) sA={sA} lB={lB}"
              f"  m0+m1")
    print()
    NI += len(z1); M0 += len(z1); M1 += len(z1)
print(f"# Part B total: {NI} instances  ->  {M0} linear runs + {M1} loop-complete"
      f" runs = {M0+M1} runs")
assert TOT == 200 and NI == 631 and M0 == 631 and M1 == 480, (TOT, NI, M0, M1)
print("# ASSERTIONS OK: 200 configurations, 631 instances, 631+480 = 1111 runs")
