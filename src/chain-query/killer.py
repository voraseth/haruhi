"""killer.py -- decide each target-cell profile with the ENDS-n6 coupling:
at kk=1 (exactly one non-cycle nc-run) the unique m=2 path component
[P1]->cnl[nc]->ps[P2] has l1+l2 <= 4; P2 is the FIRST path of the (unique
remaining) ps-headed chain and P1 the LAST path of the cnl-ended chain.
Every candidate chain decomposition is checked against the exhaustive
endpoint-pinned enumerator chainq (WLOG head 123456)."""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("killer: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import select, sys, os, re, subprocess, itertools, functools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'class-scanner'))
import scan871 as S
sys.path.insert(0, HERE)
import scanhigh as H


PROC = subprocess.Popen([os.path.join(HERE, 'chainq')], stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE, text=True, bufsize=1)
QCACHE = {}
QCOUNT = [0]
ECHO = re.compile(r'^Q c=(\d+) s5=(\d+) s4=(\d+) lf=(\d+) lb=(\d+) B=(\d+) : '
                  r'(YES|NO) nodes=(\d+)$')

def driver_error(msg):
    """A negative verdict is recorded ONLY from a complete, echo-matched answer.
    Anything else is a DRIVER-ERROR, never a kill: a dead chainq would make
    every later query answer NO, which is the verdict this program is looking
    for, so an unchecked read is a verdict-fabrication path."""
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
    key = (c, s5, s4, lf, lb, B)
    if key in QCACHE: return QCACHE[key]
    try:
        PROC.stdin.write(f"{c} {s5} {s4} {lf} {lb} {B}\n")
        PROC.stdin.flush()
    except (BrokenPipeError, ValueError):
        driver_error(f"chainq is not accepting input (rc={PROC.poll()}) "
                     f"for query {key}")
    line = _readline_or_die(f"query {key}")
    if line == '':
        driver_error(f"chainq closed its output (rc={PROC.poll()}) on query "
                     f"{key}; every later answer would read as NO")
    m = ECHO.match(line.strip())
    if not m:
        driver_error(f"unparsable chainq answer {line.strip()!r} to query {key}")
    if tuple(int(x) for x in m.group(1, 2, 3, 4, 5, 6)) != key:
        driver_error(f"chainq echo {m.group(0)!r} does not match the query "
                     f"{key} that was sent: answers are desynchronised")
    QCOUNT[0] += 1
    r = m.group(7) == 'YES'
    QCACHE[key] = r
    print("    ", line.strip())
    return r

C2_HITS = [0]   # how often the C-2 empty-range state was actually reached

def comps_ok(c, s5, s4):
    return 0 <= c and 0 <= s5 and 0 <= s4 and s5 + 2*s4 <= c <= s5 + 4*s4

CT = None
def free_cap(k, m, q5, q4):
    """certified max blocks over k unconstrained chains, exact totals."""
    if k == 0:
        return 0 if (m == 0 and q5 == 0 and q4 == 0) else None
    return S.FC(k, m, q5, q4, 0, 0, CT)

def profile_alive(w, D, X4, Z):
    """True if some coupled decomposition survives; kk=0 profiles -> alive
    (this tooth abstains there)."""
    Pn, e, Ncyc, NCh = w['Pnum'], w['e'], w['Ncyc'], w['NCh']
    S5, S4 = w['S5'], w['S4']
    Fp = Pn - S5 - S4
    Ncomp = Pn - w['cnl'] + Ncyc
    for c2 in range(0, Ncyc+1):
        c1 = Ncyc - c2
        if S5 < c1 or S4 < 2*c2: continue
        kk = e - (c1 + 2*c2)
        if kk < 0: continue
        dfc = (D - S5) - 7*c2
        if dfc < 0: continue
        if not H._pfeas(Ncomp - Ncyc, kk, Fp, S5-c1, S4-2*c2, dfc): continue
        npin = c1 + 2*c2
        rem_k, mr = NCh - npin, D - c1 - 7*c2
        q5r, q4r = S5 - c1, S4 - 2*c2
        need = Pn - npin
        hs = e - npin
        if hs != kk:
            print(f"    !! hs={hs} kk={kk} unexpected"); return True
        if kk == 0:
            # no coupling; certified free caps only (heads q1/d4, tails q720/d4)
            v = free_cap(rem_k, mr, q5r, q4r)
            if v is not None and v >= need:
                print(f"    kk=0 c1={c1} c2={c2}: free caps give {v} >= {need} -> alive")
                return True
            continue
        if kk != 1:
            print(f"    kk={kk} > 1: tooth not implemented -> alive"); return True
        for l1 in (1, 2, 3):
            for l2 in (1, 2, 3):
                if l1 + l2 > 4: continue
                # both P1,P2 are s4 paths; packing at kk=1: rest are singleton
                # comps (always packable); deficiency bookkeeping is global.
                # SAME-chain case: A = ps+cnl, others free
                for s4A in range(2, q4r+1):
                    for s5A in range(0, q5r+1):
                        for cA in range(s5A+2*s4A, min(s5A+4*s4A, mr)+1):
                            rest = (rem_k-1, mr-cA, q5r-s5A, q4r-s4A)
                            fc = free_cap(*rest)
                            if fc is None: continue
                            if query(cA, s5A, s4A, l2, l1, need - fc):
                                print(f"    SURVIVES same-chain: (l1,l2)=({l1},{l2}) "
                                      f"A=({cA},{s5A},{s4A}) needA={need-fc}")
                                return True
                # DIFF: A = ps+q720 (lf=l2), B = q1+cnl (lb=l1), rest free
                if rem_k >= 2:
                    for s4A in range(1, q4r+1):
                        for s5A in range(0, q5r+1):
                            for cA in range(s5A+2*s4A, min(s5A+4*s4A, mr)+1):
                                for s4B in range(1, q4r-s4A+1):
                                    for s5B in range(0, q5r-s5A+1):
                                        for cB in range(s5B+2*s4B, min(s5B+4*s4B, mr-cA)+1):
                                            rest = (rem_k-2, mr-cA-cB, q5r-s5A-s5B, q4r-s4A-s4B)
                                            fc = free_cap(*rest)
                                            if fc is None: continue
                                            # C-2 guard.  When the free chains
                                            # alone already supply MORE blocks
                                            # than are needed, `range(need-fc,
                                            # -1, -1)` is EMPTY, so the branch
                                            # below would silently do nothing
                                            # and the decomposition would be
                                            # reported KILLED without being
                                            # examined.  It is alive.
                                            if need - fc < 0:
                                                C2_HITS[0] += 1
                                                print(f"    SURVIVES diff-chain "
                                                      f"(free chains alone give "
                                                      f"{fc} >= need {need})")
                                                return True
                                            for tA in range(need - fc, -1, -1):
                                                if not query(cA, s5A, s4A, l2, 0, tA): continue
                                                if query(cB, s5B, s4B, 0, l1, need - fc - tA):
                                                    print(f"    SURVIVES diff-chain (l1,l2)=({l1},{l2})")
                                                    return True
                                                break
    return False

def positive_control():
    """F3.  A chainq that answers a well-formed NO to EVERY query would make
    this program report every cell CELL DEAD -- a STRONGER claim than the truth
    -- at exit 0, and the echo check cannot see it because the echo is correct.
    The protection used to be external only (run.sh runs qvalid.py next under
    set -e).  So: before any NO is believed, demand a YES that the mathematics
    guarantees.  A 4-block chain all of whose link-paths have length 5 exists
    and is the certified C6-A maximum; a 5-block one does not."""
    if not query(0, 0, 0, 0, 0, 4):
        driver_error("POSITIVE CONTROL FAILED -- chainq cannot find a 4-block "
                     "all-length-5 chain, which is the certified C6-A maximum "
                     "and must exist; every KILLED below would be void")
    if query(0, 0, 0, 0, 0, 5):
        driver_error("NEGATIVE CONTROL FAILED -- chainq claims a 5-block "
                     "all-length-5 chain, which C6-A forbids; the oracle is "
                     "not the certified enumerator")
    print("  positive control: 4-block all-length-5 chain YES, 5-block NO "
          "(the C6-A boundary) -- the oracle discriminates")


if __name__ == '__main__':
    CT = S.ct_key(4, 2, 0, 0, 4)
    print("== oracle controls (F3) ==")
    positive_control()
    # the two control queries are NOT part of the elimination battery, whose
    # size (5544) is a published figure; reset the counters so the battery total
    # below stays exactly comparable with CERTIFICATES/killer1.log
    NCONTROL = QCOUNT[0]
    QCOUNT[0] = 0
    # G-2: the backstop below must count YES answers from the BATTERY only.  The
    # two control queries are already cached as YES/NO, so counting all of QCACHE
    # would let an oracle that answers the controls correctly and NO to every
    # real query pass the `yes == 0` gate and fabricate a CELL DEAD.
    CTRL_KEYS = set(QCACHE)
    TARGETS = [(20,0,0,e) for e in (5,6,7,8,9)] + [(15,1,0,7)]
    summary = []
    for (D,X4,Z,e) in TARGETS:
        ws = S.cell_witnesses(D, X4, Z, e, 0, H.ON, first_only=False)
        ws = [w for w in ws if H.highe_ok(w, D, X4, Z)]
        alive = 0
        print(f"== ({D},{X4},{Z}) e={e}: {len(ws)} profiles into ENDS-n6 ==")
        for w in ws:
            print(f"  profile Ncyc={w['Ncyc']} S5={w['S5']} S4={w['S4']} NCh={w['NCh']}:")
            a = profile_alive(w, D, X4, Z)
            print(f"  -> {'ALIVE' if a else 'KILLED'}")
            alive += a
        summary.append(((D,X4,Z,e), len(ws), alive))
    print("\n==== SUMMARY ====")
    for cell, n, alive in summary:
        print(f"  {cell}: {n} profiles, {alive} alive "
              f"[{'CELL DEAD' if alive == 0 else 'cell alive'}]")
    print("queries:", QCOUNT[0])
    print(f"(plus {NCONTROL} oracle-control queries, not part of the battery)")
    print("C-2 empty-range states reached (diff-chain, need-fc<0):", C2_HITS[0])
    battery = {k: v for k, v in QCACHE.items() if k not in CTRL_KEYS}
    yes = sum(1 for v in battery.values() if v)
    print(f"YES answers across the battery: {yes} of {len(battery)} distinct "
          f"queries (controls excluded)")
    if yes == 0:
        driver_error("no BATTERY query answered YES: an oracle that answers the "
                     "two controls correctly and NO to everything else produces "
                     "exactly this transcript, and every CELL DEAD above would "
                     "be void.  The mathematics guarantees real YES answers "
                     "exist here: 136 of the 5544 battery queries in the "
                     "committed run, plus the control's own YES)")
    if not TARGETS or not summary:
        driver_error("zero cells scanned; there is no result to report")
    if PROC.poll() not in (None, 0):
        print(f"DRIVER-ERROR: chainq exited rc={PROC.poll()}", file=sys.stderr)
        sys.exit(3)
