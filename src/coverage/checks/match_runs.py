#!/usr/bin/env python3
"""match_runs.py -- close the last link of the chain: the 631 instances I derive
independently are EXACTLY the 1111 committed runs of CERTIFICATES/sweep_all.log (631 mode-0 + 480 mode-1), and every run is UNSAT EXHAUSTED."""
import sys, os, re, ast
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, HERE)
from census_gen import instances_of_cell, z1_instances, Z0_CLASSES

fail = 0
def check(n, ok, x=''):
    global fail
    print(f"  [{'PASS' if ok else 'FAIL'}] {n}{(' :: ' + x) if x else ''}")
    if not ok: fail += 1

# ---- my run list, in the driver's own tag format
mine = set()
for (D, X4, e, X4h) in Z0_CLASSES:
    pre = {20: '20', 15: '15', 10: '10'}[D]
    for (n5, n4, n3, n2, n1, c1, s2v, bq1) in instances_of_cell(D, X4, e, X4h):
        tag = (f"{pre}-e{e} n5={n5} n4={n4} S={n3},{n2},{n1} c1={c1} "
               f"s2={tuple(sorted(s2v))} bq1={bq1}")
        mine.add((tag, 0))
        if s2v: mine.add((tag, 1))
for (n5, n4, n3, n2, n1, sA, lB) in z1_instances():
    for name in ('zh', 'zp3'):
        tag = f"z1-{name} n5={n5} n4={n4} S={n3},{n2},{n1} sA={sA} lB={lB}"
        mine.add((tag, 0)); mine.add((tag, 1))

# ---- the committed log
log = os.path.join(ROOT, 'CERTIFICATES', 'sweep_all.log')
runs, verdicts, capped = set(), {}, []
pat = re.compile(r'^\[\d+/\d+\] (.*) m(\d): (\S+)(.*)$')
for line in open(log):
    m = pat.match(line.strip())
    if not m: continue
    tag, mode, verdict = m.group(1).strip(), int(m.group(2)), m.group(3)
    runs.add((tag, mode)); verdicts[(tag, mode)] = verdict
    if verdict not in ('SAT', 'UNSAT') or 'CAPPED' in line or 'TIMEOUT' in line:
        capped.append(line.strip())

print("== the 1111 committed runs vs my independently derived instance list ==")
check(f"committed run count = 1111", len(runs) == 1111, f"{len(runs)}")
check(f"my run count = 1111", len(mine) == 1111, f"{len(mine)}")
check("run sets are IDENTICAL (0 missing, 0 extra)", mine == runs,
      f"missing-from-log={len(mine-runs)} extra-in-log={len(runs-mine)}")
for t in sorted(mine - runs)[:6]: print("    MISSING FROM LOG:", t)
for t in sorted(runs - mine)[:6]: print("    EXTRA IN LOG:", t)
n0 = sum(1 for _, m in runs if m == 0); n1 = sum(1 for _, m in runs if m == 1)
check(f"split = 631 linear + 480 loop-complete", (n0, n1) == (631, 480), f"{n0}+{n1}")
sat = [k for k, v in verdicts.items() if v == 'SAT']
check("0 SAT verdicts", not sat, f"{len(sat)}")
check("0 CAPPED / TIMEOUT / anomalous verdicts", not capped, f"{len(capped)}")

# per-cell exposed counts
from collections import Counter
exp = Counter()
for (tag, m) in mine:
    if m == 1: exp[tag.split('-')[0]] += 1
# sorted: a Counter built from a set of string keys otherwise prints in an order
# that follows Python's per-process string-hash randomisation, which made this
# one line of the committed log not byte-reproducible across runs.
print(f"  loop-exposed per corner: {dict(sorted(exp.items()))}")
check("exposed = 256 (20,0,0) + 34 (15,1,0) + 190 (15,0,1)",
      exp['20'] == 256 and exp['15'] == 34 and exp['z1'] == 190 and exp['10'] == 0)
print(f"\n{'RUN-LEVEL MATCH COMPLETE' if fail == 0 else f'{fail} FAILURES'}")
sys.exit(1 if fail else 0)
