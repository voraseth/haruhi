#!/usr/bin/env python3
# mkjobs.py -- generate and run every stage-2 job for the (20,0,0) cells.
# For each surviving K3 census row (a2,a3,c1,c2,bq1,n45,n4) [all have a3=c2=0]
# the free variables are the short-length multiset S (|S| = a1-n45, entries
# 1..3) and the M2 cost multiset (a2 entries s2 in 2..4), tied by the single
# class-budget identity  5*n5 + 4*n4 + sum(S) + 4*c1 + sum(s2) = 120.
# (The D-ledger identity is equivalent given P# and the census -- checked.)
import os, sys, subprocess, itertools
# resolve imports and the engine path from THIS file, not from the caller's cwd
# (the released layout has no `checks/` subdirectory; the old relative paths
# raised ImportError before anything ran)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tight_enum import enumerate_cell

def short_multisets(k, total):
    if k == 0:
        return [()] if total == 0 else []
    out = []
    def rec(k, total, mx, cur):
        if k == 0:
            if total == 0: out.append(tuple(cur))
            return
        for v in range(min(mx, total - (k-1)), 0, -1):
            if total - v > 3*(k-1): continue
            rec(k-1, total-v, v, cur+[v])
    rec(k, total, 3, [])
    return out

def jobs_for(e, cap, D=20, X4=0, X4h=0):
    cfgs = sorted(set(enumerate_cell(D, X4, e, X4h, "", quiet=True)))
    rows = sorted(set((o[0], o[4], o[5], o[6]) for o in cfgs))   # (a2,bq1,n45,n4)
    seen = set()
    jobs = []
    P = 24 + D // 5
    for (a2, bq1, n45, n4) in rows:
        c1 = e - a2
        a1 = P - e - a2
        nS = a1 - n45
        n5 = n45 - n4
        T = 120 - 5*n5 - 4*n4 - 4*c1          # = sum(S) + sum(s2)
        for s2v in itertools.combinations_with_replacement((2,3,4), a2):
            sigma = T - sum(s2v)
            for S in short_multisets(nS, sigma):
                n3 = S.count(3); n2 = S.count(2); n1 = S.count(1)
                key = (n5, n4, n3, n2, n1, c1, s2v, bq1)
                if key in seen: continue
                seen.add(key)
                jobs.append(key)
    return jobs

_ENGDIR = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       os.pardir, 'engine-original')

# realize2/3's exit convention: 0 = SAT, 2 = UNSAT (exhausted), 3 = NODE_CAP_HIT,
# 1 = usage / startup table failure.  A cell is declared EMPTY only if every run
# exited 2 with the UNSAT ... EXHAUSTED marker; anything else is a DRIVER-ERROR.
def classify(rc, line):
    if line.startswith('UNSAT ') and 'EXHAUSTED' in line and rc == 2: return 'UNSAT'
    if line.startswith('SAT ') and rc == 0: return 'SAT'
    if ('NODE_CAP_HIT' in line or 'CAPPED' in line) and rc == 3: return 'CAPPED'
    return 'DRIVER-ERROR'

def run(e, cap='4000000000', D=20, X4=0, X4h=0):
    jobs = jobs_for(e, cap, D, X4, X4h)
    print(f"== ({D},{X4},0) e={e} X4h={X4h}: {len(jobs)} jobs ==")
    # G-3 / N-1: zero work is not an empty cell.  With len(jobs)==0 every counter
    # below is 0, so the ns==nc==ne==0 condition holds and the emptiness banner
    # would print for a cell nothing was run on -- exactly the N-1 failure mode.
    if not jobs:
        sys.exit(f"DRIVER-ERROR: ({D},{X4},0) e={e} X4h={X4h} generated 0 jobs; "
                 f"nothing was searched, so the cell is NOT established empty")
    verdicts = []
    for (n5, n4, n3, n2, n1, c1, s2v, bq1) in jobs:
        s2s = ','.join(map(str, s2v)) if s2v else '0'
        eng = os.path.join(_ENGDIR, 'realize2' if X4h == 0 else 'realize3')
        cmd = [eng, str(n5), str(n4), str(n3), str(n2), str(n1),
               str(c1), s2s, str(bq1)] + ([str(X4h)] if X4h else []) + [cap]
        r = subprocess.run(cmd, capture_output=True, text=True)
        line = r.stdout.splitlines()[0] if r.stdout else f'ENGINE ERROR rc={r.returncode}'
        tag = f"n5={n5} n4={n4} S=({n3}x3,{n2}x2,{n1}x1) c1={c1} s2={s2s} bq1={bq1}"
        kind = classify(r.returncode, line)
        print(f"  {tag}: {line}" + (f"   [{kind} rc={r.returncode}]"
                                    if kind != 'UNSAT' else ''))
        verdicts.append(kind)
    ns = verdicts.count('SAT'); nc = verdicts.count('CAPPED')
    ne = verdicts.count('DRIVER-ERROR'); nu = verdicts.count('UNSAT')
    print(f"  --> e={e}: {ns} SAT, {nc} CAPPED, {ne} DRIVER-ERROR, "
          f"{nu} UNSAT-EXHAUSTED"
          + ("   *** CELL EMPTY ***" if ns == 0 and nc == 0 and ne == 0 else ""))
    if ne:
        sys.exit(f"DRIVER-ERROR: {ne} of {len(verdicts)} runs in e={e} produced "
                 f"no usable verdict; the cell is NOT established empty")
    # F2: an accepting or capped run is not an emptiness result, and must reach
    # the exit status -- a `set -e` wrapper would otherwise not notice it.
    if ns or nc:
        sys.exit(f"e={e}: {ns} SAT and {nc} CAPPED runs; a capped run "
                 f"establishes nothing and an accepting one refutes emptiness")
    return True

if __name__ == '__main__':
    if sys.argv[1] == 'corner15':
        cap = sys.argv[2] if len(sys.argv) > 2 else '4000000000'
        for e in (7,4,3,2,1):
            run(e, cap, D=15, X4=1, X4h=1)
    elif sys.argv[1] == 'corner10':
        cap = sys.argv[2] if len(sys.argv) > 2 else '4000000000'
        run(2, cap, D=10, X4=2, X4h=2)
    else:
        es = [int(x) for x in sys.argv[1].split(',')]
        cap = sys.argv[2] if len(sys.argv) > 2 else '4000000000'
        for e in es:
            run(e, cap)
