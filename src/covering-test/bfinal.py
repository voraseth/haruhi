"""bfinal.py -- COMPLETE exact-split sweep for the two 2-chain profiles:
(B) (20,0,0) e=7 Ncyc=6 (kk=1, coupled) and (C) (15,1,0) e=7 Ncyc=7 (kk=0).
Every exact configuration (chain compositions + block split + coupling) is
pre-filtered by chainq (>= queries, necessary) and, if it passes, certified
by cover (exact enumeration + rho-4-segment partition of the leftover)."""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("bfinal: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import select, sys, os, re, subprocess, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
PROC = subprocess.Popen([os.path.join(HERE, 'chainq')], stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE, text=True, bufsize=1)
CACHE = {}
NCOVER = [0]
ECHO = re.compile(r'^Q c=(\d+) s5=(\d+) s4=(\d+) lf=(\d+) lb=(\d+) B=(\d+) : '
                  r'(YES|NO) nodes=(\d+)$')

def driver_error(msg):
    """chainq is only a PRE-FILTER here, and a False from it SKIPS the cover
    enumeration.  So a dead chainq would answer NO to everything and this script
    would print `0 cover runs, 0 alive [PROFILE EMPTY]` without ever running
    `cover`.  Every read is therefore checked, and every failure is fatal."""
    print(f"DRIVER-ERROR: {msg}", file=sys.stderr)
    print(f"DRIVER-ERROR: {msg}")
    sys.exit(3)

# F4 watchdog.  A chainq that drops ONE answer but stays alive would deadlock
# this driver forever on readline(): no verdict, no error, no exit.  Safe in
# direction -- nothing is fabricated -- but silent.  READ_TIMEOUT turns it into
# a loud DRIVER-ERROR.  The budget is deliberately generous: the slowest single
# committed query is well under a minute, so 30 minutes cannot fire on a healthy
# run and does fire on a hung one.
READ_TIMEOUT = float(os.environ.get('CHAINQ_READ_TIMEOUT', 1800))

def _readline_or_die(what):
    r, _, _ = select.select([PROC.stdout], [], [], READ_TIMEOUT)
    if not r:
        driver_error(f"chainq produced no answer within {READ_TIMEOUT:.0f}s "
                     f"for {what} (rc={PROC.poll()}); a dropped answer would "
                     f"otherwise deadlock this driver silently")
    return PROC.stdout.readline()

def query(c, s5, s4, lf, lb, B):
    if B <= 0: return True
    k = (c, s5, s4, lf, lb, B)
    if k not in CACHE:
        try:
            PROC.stdin.write(f"{c} {s5} {s4} {lf} {lb} {B}\n")
            PROC.stdin.flush()
        except (BrokenPipeError, ValueError):
            driver_error(f"chainq is not accepting input (rc={PROC.poll()}) "
                         f"for query {k}")
        line = _readline_or_die(f"query {k}")
        if line == '':
            driver_error(f"chainq closed its output (rc={PROC.poll()}) on query {k}")
        m = ECHO.match(line.strip())
        if not m:
            driver_error(f"unparsable chainq answer {line.strip()!r} to query {k}")
        if tuple(int(x) for x in m.group(1, 2, 3, 4, 5, 6)) != k:
            driver_error(f"chainq echo {m.group(0)!r} does not match the query {k} "
                         f"that was sent: answers are desynchronised")
        CACHE[k] = m.group(7) == 'YES'
    return CACHE[k]

def cover(nq, spec1, spec2):
    args = [os.path.join(HERE, 'cover'), str(nq)] + [str(v) for v in spec1] + \
           [str(v) for v in spec2]
    r = subprocess.run(args, capture_output=True, text=True)
    if r.returncode != 0:
        driver_error(f"cover exited rc={r.returncode} on {args[1:]}")
    out = r.stdout
    cand = [l for l in out.splitlines() if 'configs=' in l]
    if len(cand) != 1:
        driver_error(f"cover printed {len(cand)} verdict lines on {args[1:]}")
    NCOVER[0] += 1
    line = cand[0]
    print("   ", ' '.join(str(v) for v in spec1), '|',
          ' '.join(str(v) for v in spec2), '->', line)
    return 'ALIVE' in line

def sweep(name, nq, mr, q4r, need, coupled):
    print(f"== {name}: mr={mr} q4r={q4r} need={need} coupled={coupled} ==")
    alive = 0; ncov = 0
    ends = [(l1, l2) for l1 in (1,2,3) for l2 in (1,2,3) if l1+l2 <= 4] \
           if coupled else [(0, 0)]
    for (l1, l2) in ends:
        for s4A in range(0, q4r+1):
            s4B = q4r - s4A
            for cA in range(2*s4A, min(4*s4A, mr)+1):
                cB = mr - cA
                if not (2*s4B <= cB <= 4*s4B): continue
                for tA in range(max(1, s4A), need):
                    tB = need - tA
                    if tB < max(1, s4B): continue
                    if coupled:
                        # same-chain (A carries both) and diff-chain cases
                        for (lfA, lbA, lfB, lbB) in (((l2, l1, 0, 0)),
                                                     ((l2, 0, 0, l1))):
                            if lfA and s4A < 1: continue
                            if lbA and s4A < (2 if lfA else 1): continue
                            if lbB and s4B < 1: continue
                            if not query(cA, 0, s4A, lfA, lbA, tA): continue
                            if not query(cB, 0, s4B, lfB, lbB, tB): continue
                            ncov += 1
                            if cover(nq, (cA,0,s4A,lfA,lbA,tA),
                                         (cB,0,s4B,lfB,lbB,tB)): alive += 1
                    else:
                        if not query(cA, 0, s4A, 0, 0, tA): continue
                        if not query(cB, 0, s4B, 0, 0, tB): continue
                        ncov += 1
                        if cover(nq, (cA,0,s4A,0,0,tA), (cB,0,s4B,0,0,tB)):
                            alive += 1
    print(f"  {name}: {ncov} cover runs, {alive} alive "
          f"[{'PROFILE EMPTY' if alive == 0 else 'ALIVE'}]")
    return alive

def sweep1(name, nq, mr, q4r, need):
    """single-remaining-chain profile: the one chain carries all totals."""
    print(f"== {name}: single chain ({mr},0,{q4r}) blocks={need} ==")
    if not query(mr, 0, q4r, 0, 0, need):
        print(f"  {name}: no such chain at all [PROFILE EMPTY]"); return 0
    args = [os.path.join(HERE, 'cover'), str(nq),
            str(mr), '0', str(q4r), '0', '0', str(need)]
    r = subprocess.run(args, capture_output=True, text=True)
    if r.returncode != 0:
        driver_error(f"cover exited rc={r.returncode} on {args[1:]}")
    cand = [l for l in r.stdout.splitlines() if 'configs=' in l]
    if len(cand) != 1:
        driver_error(f"cover printed {len(cand)} verdict lines on {args[1:]}")
    NCOVER[0] += 1
    line = cand[0]
    print("   ", line)
    alive = 1 if 'ALIVE' in line else 0
    print(f"  {name}: [{'PROFILE EMPTY' if alive == 0 else 'ALIVE'}]")
    return alive

def positive_control():
    """the verified 872's shape: one 4-full-block chain + 25 T1 quads MUST
    come back ALIVE, or the cover machinery is broken."""
    args = [os.path.join(HERE, 'cover'), '25', '0','0','0','0','0','4']
    r = subprocess.run(args, capture_output=True, text=True)
    if r.returncode != 0:
        driver_error(f"cover exited rc={r.returncode} on the positive control")
    cand = [l for l in r.stdout.splitlines() if 'configs=' in l]
    if len(cand) != 1:
        driver_error("cover printed no verdict line on the positive control")
    line = cand[0]
    print("== POSITIVE CONTROL (verified-872 shape) ==\n   ", line)
    if 'ALIVE' not in line:
        driver_error("POSITIVE CONTROL FAILED -- cover.c does not find the "
                     "length-872 witness's own shape; every EMPTY below is void")
    # the pre-filter must also be alive before any of its NOs is believed
    if not query(0, 0, 0, 0, 0, 4):
        driver_error("chainq PRE-FILTER CONTROL FAILED -- a 4-block all-length-5 "
                     "chain is the certified C6-A maximum and must exist")
    print("    chainq pre-filter control: 4-block all-length-5 chain found (YES)")
    return True

positive_control()
aA = sweep1("A (20,0,0) e=6 Ncyc=6", 6, 14, 6, 22)
aB = sweep("B (20,0,0) e=7 Ncyc=6", 6, 14, 6, 22, True)
aC = sweep("C (15,1,0) e=7 Ncyc=7", 7, 8, 4, 20, False)
print("FINAL:", "A", "EMPTY" if aA == 0 else "ALIVE", "/",
      "B", "EMPTY" if aB == 0 else "ALIVE", "/",
      "C", "EMPTY" if aC == 0 else "ALIVE")
print(f"cover invocations: {NCOVER[0]} (1 positive control + the sweeps)")
if NCOVER[0] < 2:
    driver_error(f"only {NCOVER[0]} cover invocations: the sweeps ran no enumeration")
if PROC.poll() not in (None, 0):
    print(f"DRIVER-ERROR: chainq exited rc={PROC.poll()}", file=sys.stderr)
    sys.exit(3)
if aA or aB or aC:
    sys.exit("a profile is ALIVE: not an emptiness result")
