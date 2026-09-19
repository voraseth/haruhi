#!/usr/bin/env python3
"""diffcheck.py -- fidelity certificate for checks/census.py.

(1) SURVIVOR-SET EQUALITY.  census.survivors must equal tight_enum's
    enumerate_cell survivor set (projected to the 7 free coordinates) on all
    16 habitat cells and all 6 control cells, with c2 free.
(2) FRONTIER AGREEMENT.  census.py's F (built on this workdir's own
    re-enumerated table, logs/frontier_c16.log) must agree with tight_enum's F
    on the whole range consumed by the three lemmas.
(3) MODE ROBUSTNESS.  Repeat (1) with cap-mode 'lin' (C6-B only beyond cost
    16, dropping the registered g(20)=25): survivor sets must be supersets,
    and the c2>=1 verdicts must be unchanged (checked in lem67_c2.py).
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("diffcheck: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import sys
import os
_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.abspath(os.path.join(_HERE, '..', '..', '..'))
sys.path.insert(0, _HERE)
sys.path.insert(0, os.path.join(_ROOT, 'src', 'class-elimination'))
import tight_enum
import frontier
import census


CELLS = ([(20, 0, e, 0) for e in range(1, 10)] +
         [(15, 1, e, 1) for e in (1, 2, 3, 4, 7)] +
         [(10, 2, 2, 1), (10, 2, 2, 2)])
CONTROLS = [(25, 0, 25, 0)] + [(0, 6, 0, x) for x in (2, 3, 4, 5, 6)]

ok = True

# (2) frontier agreement over the consumed range
bad = 0
for k in range(1, 6):
    for m in range(0, 21):
        for sh in range(0, 3):
            for st in range(0, 3):
                a = tight_enum.F(k, m, sh, st)
                b = frontier.F(k, m, sh, st)
                if a != b:
                    bad += 1
                    if bad <= 5:
                        print(f"  F MISMATCH k={k} m={m} sh={sh} st={st}: "
                              f"tight_enum={a} finlem={b}")
print(f"(2) FRONTIER AGREEMENT over k<=5, cost<=20, sh,st<=2: "
      f"{'PASS' if bad == 0 else f'FAIL ({bad} mismatches)'}")
ok &= (bad == 0)

# (1) survivor-set equality
mism = []
for D, X4, e, X4h in CELLS + CONTROLS:
    a = sorted(o[:7] for o in tight_enum.enumerate_cell(D, X4, e, X4h, "",
                                                        quiet=True))
    b = sorted(census.survivors(D, e, X4h))
    if a != b:
        mism.append((D, X4, e, X4h, len(a), len(b)))
print(f"(1) SURVIVOR-SET EQUALITY on {len(CELLS)} habitat + {len(CONTROLS)} "
      f"control cells: {'PASS' if not mism else 'FAIL ' + str(mism)}")
ok &= not mism

# (3) mode robustness: 'lin' must over-cover 'full'
frontier.set_mode('lin')
sup = True
for D, X4, e, X4h in CELLS + CONTROLS:
    frontier.set_mode('full')
    a = set(census.survivors(D, e, X4h))
    frontier.set_mode('lin')
    b = set(census.survivors(D, e, X4h))
    if not a <= b:
        sup = False
        print(f"  LIN NOT A SUPERSET at ({D},{X4},0) e={e} X4h={X4h}")
frontier.set_mode('full')
print(f"(3) MODE ROBUSTNESS (cap-mode 'lin' over-covers 'full'): "
      f"{'PASS' if sup else 'FAIL'}")
ok &= sup

print("DIFFERENTIAL:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
