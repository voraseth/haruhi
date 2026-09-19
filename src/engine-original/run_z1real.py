#!/usr/bin/env python3
# run_z1real.py -- stage-2 realizability battery for (15,0,1) e=2 (both K2
# wirings).  Job space: (span budgets) x (a1 deficiency splits), from the
# identities  sum(def_a1) = sA + l''  (zh)  resp.  s1 + l3  (zp3),
# def per short in {2,3,4} (length 5-def), fours def 1.
import os, subprocess, sys
# resolve the engine from THIS file, not the caller's cwd (same class
# of defect as mkjobs.py's former './checks/realize2')
_ENG = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'realize4')
def short_defsets(total):
    out = []
    def rec(total, mx, cur):
        if total == 0: out.append(tuple(cur)); return
        for v in range(min(mx, total), 1, -1):
            rec(total - v, v, cur + [v])
    rec(total, 4, [])
    return out
def jobs(mode):
    # mode 1 = zh (spanA=sA, spanB=l''), mode 2 = zp3 (s1, l3)
    out = []
    for sA in (2, 3, 4):
        for lB in (1, 2, 3, 4):
            B = sA + lB
            for n4 in range(0, B + 1):
                for ds in short_defsets(B - n4):
                    nS = len(ds)
                    n5 = 24 - n4 - nS
                    if n5 < 0: continue
                    n3 = ds.count(2); n2 = ds.count(3); n1 = ds.count(4)
                    out.append((n5, n4, n3, n2, n1, sA, lB))
    return sorted(set(out))
# realize4's exit convention: 0 = SAT, 2 = UNSAT (exhausted), 3 = NODE_CAP_HIT.
# A wiring is declared dead only if every run exited 2 with the UNSAT ...
# EXHAUSTED marker; anything else is a DRIVER-ERROR, never a kill.
def classify(rc, line):
    if line.startswith('UNSAT ') and 'EXHAUSTED' in line and rc == 2: return 'UNSAT'
    if line.startswith('SAT ') and rc == 0: return 'SAT'
    if ('NODE_CAP_HIT' in line or 'CAPPED' in line) and rc == 3: return 'CAPPED'
    return 'DRIVER-ERROR'

cap = sys.argv[1] if len(sys.argv) > 1 else '4000000000'
for mode, name in ((1, 'zh'), (2, 'zp3')):
    js = jobs(mode)
    print(f"== (15,0,1) e=2, {name} wiring: {len(js)} jobs ==", flush=True)
    # N-1: zero work is not a dead wiring.
    if not js:
        sys.exit(f"DRIVER-ERROR: wiring {name} generated 0 jobs; nothing was "
                 f"searched, so the wiring is NOT established dead")
    if len(js) != 95:
        sys.exit(f"DRIVER-ERROR: wiring {name} generated {len(js)} jobs, "
                 f"expected 95 (95 x 2 wirings = the 190 defect instances)")
    nsat = ncap = nerr = nuns = 0
    for (n5, n4, n3, n2, n1, sA, lB) in js:
        cmd = [_ENG, str(n5), str(n4), str(n3), str(n2), str(n1),
               '0', str(sA), '0', str(mode), str(lB), cap]
        r = subprocess.run(cmd, capture_output=True, text=True)
        line = r.stdout.splitlines()[0] if r.stdout else f'ENGINE ERROR rc={r.returncode}'
        kind = classify(r.returncode, line)
        print(f"  n5={n5} n4={n4} S=({n3}x3,{n2}x2,{n1}x1) sA={sA} lB={lB}: {line}"
              + (f"   [{kind} rc={r.returncode}]" if kind != 'UNSAT' else ''), flush=True)
        if kind == 'SAT': nsat += 1
        elif kind == 'CAPPED': ncap += 1
        elif kind == 'DRIVER-ERROR': nerr += 1
        else: nuns += 1
    print(f"  --> {name}: {nsat} SAT, {ncap} CAPPED, {nerr} DRIVER-ERROR, "
          f"{nuns} UNSAT-EXHAUSTED"
          + ("   *** WIRING DEAD ***" if nsat == 0 and ncap == 0 and nerr == 0 else ""),
          flush=True)
    if nerr:
        sys.exit(f"DRIVER-ERROR: {nerr} of {len(js)} runs in wiring {name} produced "
                 f"no usable verdict; the wiring is NOT established dead")
    # F2: SAT / CAPPED must reach the exit status.
    if nsat or ncap:
        sys.exit(f"wiring {name}: {nsat} SAT and {ncap} CAPPED runs; a capped "
                 f"run establishes nothing and an accepting one refutes the kill")
