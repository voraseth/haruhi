#!/usr/bin/env python3
"""controls.py -- ADMISSION and DISCRIMINATION controls for the coverage chain.

ADMISSION (a coverage argument that excludes real objects is false):
  * the verified 872 (shared/best872.txt)                 corner (25,0,0), e=25
  * the verified 873 baseline (shared/baseline6.txt)      corner (0,6,0),  e=0
  * the six R-n6-7 counterexample objects m2obj_*.txt      L=877..880, a2=1..5
  For each, the object's OWN configuration (extracted from the raw string by
  the reviewer's independent analyzer) must be admitted by Algorithm G at the
  object's own class, and the proved two-loop inequality must hold for it.

DISCRIMINATION (the machinery must not accept everything):
  * per-test ablation over the 15 L=871 classes
  * cells the machinery kills outright
  * the a2=3 discrimination: the SAME tests reject a2=3 at L=871 and accept it
    where a real object has it
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("controls: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 1 `assert` statements")
import sys, os, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'src', 'coverage', 'deps'))
from census_gen import gen_cell, configs_of_cell, Z0_CLASSES
from myanalyze import analyze


fail = 0
def check(name, ok, extra=''):
    global fail
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}{(' :: ' + extra) if extra else ''}")
    if not ok: fail += 1

def object_config(path):
    """Extract the census CONFIGURATION KEY of a real superpermutation."""
    S = open(path).read().strip()
    a = analyze(S)
    assert a is not None, f"{path} is not a superpermutation"
    paths, comp_paths = a['paths'], a['comp_paths']
    L = {i: len(p) for i, p in enumerate(paths)}
    a1 = a2 = a3 = c1 = c2 = 0
    n5 = n4 = nS = 0
    sum_c1 = sum_c2 = 0
    q1cls = None
    # which component holds q1's path?
    q1path = a['path_of'][[c for c, k in a['y'].items() if a['pos'][a['order'][k]] >= 0
                           and a['order'][0] in [] ] [0]] if False else None
    # q1 = order[0]; its class:
    def cls(p):
        b = p; q = p
        for _ in range(5):
            q = q[1:] + q[:1]
            if q < b: b = q
        return b
    q1c = cls(a['order'][0]); q1p = a['path_of'][q1c]
    bq1 = 0
    for kind, pset, vs in comp_paths:
        m = len(pset)
        if kind == 'path':
            if m == 1:
                a1 += 1
                l = L[pset[0]]
                if l == 5: n5 += 1
                elif l == 4: n4 += 1
                else: nS += 1
            elif m == 2: a2 += 1
            elif m == 3: a3 += 1
            if m >= 2 and q1p in pset: bq1 = 1
        else:
            if m == 1: c1 += 1; sum_c1 += L[pset[0]]
            elif m == 2: c2 += 1; sum_c2 += sum(L[i] for i in pset)
    Delta1 = 5*a1 - (5*n5 + 4*n4) - sum(L[p[0]] for k, p, v in comp_paths
                                        if k == 'path' and len(p) == 1
                                        and L[p[0]] <= 3)
    key = (a2, a3, c1, c2, bq1, n5 + n4, n4, sum_c1, sum_c2)
    return a, key, dict(a1=a1, n5=n5, n4=n4, nS=nS, Delta1=Delta1, bq1=bq1)

OBJECTS = [
    ('data/best872.txt', 'verified 872'),
    ('data/baseline6.txt', 'verified 873 baseline'),
] + [(f'data/counterexamples/m2obj_620_{i}.txt', f'R-n6-7 counterexample #{i}')
     for i in (0, 1, 11, 14, 19, 23)]

print("== ADMISSION CONTROLS: real objects at their own classes ==")
for rel, name in OBJECTS:
    p = os.path.join(ROOT, rel)
    a, key, ex = object_config(p)
    D, X4, Z, e, X4h = a['D'], a['X4'], a['Z'], a['e'], a['X4h']
    sha = hashlib.sha256(open(p).read().strip().encode()).hexdigest()[:8]
    print(f"\n  {name}  L={a['L']} sha={sha}")
    print(f"    (D,X4,Z)=({D},{X4},{Z}) e={e} X4h={X4h} P#={a['Pn']} NCh={a['NCh']}")
    print(f"    configuration key (a2,a3,c1,c2,bq1,n45,n4,sum_c1,sum_c2) = {key}")
    if Z != 0:
        check(f"{name}: Z={Z} -- outside the Z=0 generator's scope, skipped", True)
        continue
    cfgs = set(configs_of_cell(D, X4, e, X4h))
    check(f"{name}: ADMITTED by Algorithm G ({len(cfgs)} configs in its class)",
          key in cfgs)
    # the proved two-loop inequality, evaluated on the real object
    Lam = key[0] + 2*key[1] + key[3]
    rhs = D - e - ex['Delta1']
    check(f"{name}: proved inequality 5*(a2+2a3+c2) <= D-e-Delta1 holds",
          5*Lam <= rhs, f"5*{Lam}={5*Lam} <= {D}-{e}-{ex['Delta1']}={rhs}")
    print(f"    -> the same inequality permits U = a2+2a3 up to "
          f"{max(0,(rhs)//5)} here (object has {key[0]+2*key[1]})")

print("\n== DISCRIMINATION 1: per-test ablation over the 15 L=871 classes ==")
BASE = sum(len(configs_of_cell(*c)) for c in Z0_CLASSES)
print(f"  full system: {BASE} configurations")
def ablate(name, off):
    n = sum(len(configs_of_cell(*c, off=off)) for c in Z0_CLASSES)
    print(f"  {name:34s}: {n:6d} configurations  "
          f"({'+%d revived' % (n-BASE) if n > BASE else 'no change -- VACUOUS HERE'})")
    return n
n_tc2c = ablate("TC2c cycle closure OFF", ('tc2c',))
n_run  = ablate("run caps C6-A OFF", ('runcap',))
n_val  = ablate("value ledger OFF", ('value',))
n_par  = ablate("Pareto ledger OFF", ('pareto',))
n_all  = ablate("ALL FOUR OFF (identities only)", ('tc2c','runcap','value','pareto'))
check("the machinery does NOT accept everything (identities alone admit far more)",
      n_all > 5*BASE, f"{n_all} vs {BASE}")
check("three of the four tests bite at L=871 (TC2c, run caps, Pareto)",
      min(n_tc2c, n_run, n_par) > BASE,
      f"TC2c={n_tc2c} run={n_run} pareto={n_par}")
print("  HONEST FINDING: the VALUE ledger is verdict-neutral at L=871 -- removing")
print("  it revives 0 configurations.  This reproduces the artifact's own ablation")
print("  (n6tight/checks/probe_kill.py: 'relaxing the VALUE ledger alone revives 0')")
print("  and makes the census MORE robust, not less: it does not rest on that test.")
check("TC2c-off count reproduces the artifact's pre-TC2c census (274)",
      n_tc2c == 274, f"{n_tc2c}")
# ablation must never DELETE a configuration: each test is a filter
sub = all(set(configs_of_cell(*c)) <= set(configs_of_cell(*c, off=('tc2c','runcap','value','pareto')))
          for c in Z0_CLASSES)
check("every full-system configuration survives with all tests off (monotone filters)", sub)

print("\n== DISCRIMINATION 2: cells the machinery kills outright ==")
for (D, X4, e, X4h, want) in [(10, 2, 2, 1, 0), (10, 2, 2, 2, 4),
                              (0, 6, 0, 2, 0), (0, 6, 0, 3, 0), (0, 6, 0, 4, 0),
                              (0, 6, 0, 5, 1), (0, 6, 0, 6, 1),
                              (25, 0, 25, 0, 1)]:
    n = len(configs_of_cell(D, X4, e, X4h))
    check(f"({D},{X4},0) e={e} X4h={X4h}: {n} configs (expected {want})", n == want)
print("  -> Theorem K1 (the (10,2,0)/X4h=1 quarter-kill) is reproduced;")
print("     the 873 corner is FORCED to X4h >= 5, the real 873's value;")
print("     the 872 corner admits EXACTLY ONE configuration, the real 872's.")

print("\n== DISCRIMINATION 3: the a2 = 3 test (same code, opposite verdicts) ==")
n871 = max((k[0] for c in Z0_CLASSES for k in configs_of_cell(*c)))
check("a2 <= 2 in every L=871 class (a2=3 REJECTED)", n871 <= 2, f"max a2 = {n871}")
# the class of counterexample #1 (L=877): (50,0,0) e=29, which really has a2=3
n877 = max((k[0] for k in configs_of_cell(50, 0, 29, 0)), default=-1)
check("a2 = 3 ACCEPTED at (50,0,0) e=29, where a real object has it",
      n877 >= 3, f"max a2 = {n877}")
n880 = max((k[0] for k in configs_of_cell(65, 0, 30, 0)), default=-1)
check("a2 = 5 ACCEPTED at (65,0,0) e=30, where a real object has it",
      n880 >= 5, f"max a2 = {n880}")

print(f"\n{'ALL CONTROLS PASS' if fail == 0 else f'{fail} CONTROLS FAILED'}")
sys.exit(1 if fail else 0)
