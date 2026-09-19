#!/usr/bin/env python3
# R-n6-7 sweep driver: mode 0 (full independent re-execution, all 631 jobs)
# and mode 1 (R1-free loop sweep, all M2/B-exposed jobs).
import sys, subprocess, itertools, os
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tight_enum import enumerate_cell

ENG = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'mysweep')
def multisets_le3(k, total):
    out = []
    def rec(k, total, mx, cur):
        if k == 0:
            if total == 0: out.append(tuple(sorted(cur, reverse=True)))
            return
        for v in range(mx, 0, -1):
            if v > total - (k-1) or total - v > 3*(k-1): continue
            rec(k-1, total-v, v, cur+[v])
    rec(k, total, 3, [])
    return out

def jobs_for_cell(D, X4, e, X4h):
    P = 24 + D//5
    cfgs = enumerate_cell(D, X4, e, X4h, "", quiet=True)
    rows = sorted(set((o[0], o[4], o[5], o[6]) for o in cfgs))
    jobs = set()
    for (a2, bq1, n45, n4) in rows:
        c1 = e - a2; a1 = P - e - a2; nS = a1 - n45; n5 = n45 - n4
        T = 120 - 5*n5 - 4*n4 - 4*c1
        for s2v in itertools.combinations_with_replacement((2,3,4), a2):
            for S in multisets_le3(nS, T - sum(s2v)):
                jobs.add((n5, n4, S.count(3), S.count(2), S.count(1), c1, s2v, bq1))
    return sorted(jobs)

def z1_jobs():
    out = set()
    for sA in (2,3,4):
        for lB in (1,2,3,4):
            B = sA + lB
            for n4 in range(0, B+1):
                def rec(total, mx, cur):
                    if total == 0:
                        n5 = 24 - n4 - len(cur)
                        if n5 >= 0:
                            out.add((n5, n4, cur.count(2), cur.count(3), cur.count(4), sA, lB))
                        return
                    for v in range(min(mx, total), 1, -1):
                        rec(total - v, v, cur + [v])
                rec(B - n4, 4, [])
    return sorted(out)

tasks = []   # (tag, argv, mode)
def add(tag, n5,n4,n3,n2,n1,c1,s2v,bq1,nd4,bmode,blen, modes):
    s2s = ','.join(map(str, s2v)) if s2v else '0'
    for m in modes:
        tasks.append((f"{tag} m{m}", [ENG, str(n5),str(n4),str(n3),str(n2),str(n1),
                     str(c1), s2s, str(bq1), str(nd4), str(bmode), str(blen), str(m)]))

for e in range(1, 10):
    for (n5,n4,n3,n2,n1,c1,s2v,bq1) in jobs_for_cell(20,0,e,0):
        exposed = len(s2v) > 0
        add(f"20-e{e} n5={n5} n4={n4} S={n3},{n2},{n1} c1={c1} s2={s2v} bq1={bq1}",
            n5,n4,n3,n2,n1,c1,s2v,bq1,0,0,0, [0] + ([1] if exposed else []))
for e in (1,2,3,4,7):
    for (n5,n4,n3,n2,n1,c1,s2v,bq1) in jobs_for_cell(15,1,e,1):
        exposed = len(s2v) > 0
        add(f"15-e{e} n5={n5} n4={n4} S={n3},{n2},{n1} c1={c1} s2={s2v} bq1={bq1}",
            n5,n4,n3,n2,n1,c1,s2v,bq1,1,0,0, [0] + ([1] if exposed else []))
for (n5,n4,n3,n2,n1,c1,s2v,bq1) in jobs_for_cell(10,2,2,2):
    add(f"10-e2 n5={n5} n4={n4} S={n3},{n2},{n1} c1={c1} s2={s2v} bq1={bq1}",
        n5,n4,n3,n2,n1,c1,s2v,bq1,2,0,0, [0])
for (n5,n4,n3,n2,n1,sA,lB) in z1_jobs():
    for bmode, name in ((1,'zh'),(2,'zp3')):
        add(f"z1-{name} n5={n5} n4={n4} S={n3},{n2},{n1} sA={sA} lB={lB}",
            n5,n4,n3,n2,n1,0,(sA,),0,0,bmode,lB, [0,1])

only = sys.argv[1] if len(sys.argv) > 1 else ''
tasks = [t for t in tasks if only in t[0]]
print(f"{len(tasks)} tasks", flush=True)
# N-1: zero work is not a clean sweep.  A mistyped `only` filter would otherwise
# print "0 tasks ... DONE: 0 runs" and exit 0.
if not tasks:
    sys.exit(f"DRIVER-ERROR: the filter {only!r} selected 0 of the generated "
             f"tasks; nothing was searched")
lock = __import__('threading').Lock()
results = []
# mysweep's exit convention: 0 = SAT, 2 = UNSAT (exhausted), 3 = CAPPED,
# 1 = usage / startup table failure.  A NEGATIVE (eliminating) verdict is
# recorded ONLY when the child exited 2 AND printed the UNSAT ... EXHAUSTED
# marker.  Anything else -- a crash, an OOM kill, a `usage:` line, a truncated
# stdout -- is a DRIVER-ERROR and must never be counted as an elimination.
def classify(rc, line):
    if line.startswith('UNSAT ') and 'EXHAUSTED' in line and rc == 2:
        return 'UNSAT'
    if line.startswith('SAT ') and rc == 0:
        return 'SAT'
    if ('CAPPED' in line or 'TIMEOUT' in line) and rc in (3, None):
        return 'CAPPED'
    return 'DRIVER-ERROR'

def run(t):
    tag, argv = t
    rc = None
    try:
        r = subprocess.run(argv, capture_output=True, text=True, timeout=7200)
        rc = r.returncode
        line = r.stdout.strip().splitlines()[-1] if r.stdout else f'ERR rc={rc}'
    except subprocess.TimeoutExpired:
        line = 'TIMEOUT'
    kind = classify(rc, line)
    with lock:
        results.append((tag, line, kind, rc))
        print(f"[{len(results)}/{len(tasks)}] {tag}: {line}"
              + (f"   [{kind} rc={rc}]" if kind != 'UNSAT' else ''), flush=True)

with ThreadPoolExecutor(max_workers=9) as ex:
    list(ex.map(run, tasks))

sat = [r for r in results if r[2] == 'SAT']
cap = [r for r in results if r[2] == 'CAPPED']
err = [r for r in results if r[2] == 'DRIVER-ERROR']
unsat = [r for r in results if r[2] == 'UNSAT']
print(f"\nDONE: {len(results)} runs, SAT={len(sat)}, CAPPED/TIMEOUT={len(cap)}, "
      f"DRIVER-ERROR={len(err)}, UNSAT EXHAUSTED={len(unsat)}")
for r in sat: print("SAT:", r)
for r in cap: print("CAP:", r)
for r in err: print("DRIVER-ERROR:", r)
if len(unsat) + len(sat) + len(cap) != len(tasks) or err:
    sys.exit(f"DRIVER-ERROR: {len(err)} runs produced no usable verdict; "
             f"{len(unsat)} of {len(tasks)} exhausted")
if sat or cap:
    sys.exit(f"{len(sat)} SAT and {len(cap)} capped runs: not an emptiness result")
