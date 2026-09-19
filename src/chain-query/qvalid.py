"""qvalid.py -- validate chainq against the REGISTERED certified refined
frontier gS (REFINED_TABLE literal in scan871.py, gate-certified), over the
DECISIVE range: every table row with cost <= 16, in all four typed forms.

chainq pins endpoint LENGTHS; gS pins endpoint SHORTNESS (short = len <= 4).
Mapping used (exact, since the (a,b) cells partition chains):
  free maximum      gm  = max entries          <-> query(lf=0, lb=0)
  first-short max   m10 = max(g10, g11)        <-> max over lf in 1..4, lb=0
  last-short max    m01 = max(g01, g11)        <-> lf=0, max over lb in 1..4
  both-short max    m11 = g11                  <-> max over lf, lb in 1..4
For each defined maximum m the check is: some pinned query reaches m (YES)
and no pinned query reaches m+1 (NO across the whole grid)."""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("qvalid: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import select, sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'class-scanner'))
import scan871 as S

PROC = subprocess.Popen([os.path.join(HERE, 'chainq')], stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE, text=True, bufsize=1)
NQ = [0]
ECHO = re.compile(r'^Q c=(\d+) s5=(\d+) s4=(\d+) lf=(\d+) lb=(\d+) B=(\d+) : '
                  r'(YES|NO) nodes=(\d+)$')

def driver_error(msg):
    """A `NO` is only evidence if it came from a complete, echo-matched answer.
    A dead chainq would answer NO to everything, which here reads as `the table
    is not exceeded` -- i.e. as a PASS -- so every read is checked."""
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
    key = (c, s5, s4, lf, lb, B)
    try:
        PROC.stdin.write(f"{c} {s5} {s4} {lf} {lb} {B}\n")
        PROC.stdin.flush()
    except (BrokenPipeError, ValueError):
        driver_error(f"chainq is not accepting input (rc={PROC.poll()}) "
                     f"for query {key}")
    line = _readline_or_die(f"query {key}")
    if line == '':
        driver_error(f"chainq closed its output (rc={PROC.poll()}) on query {key}")
    m = ECHO.match(line.strip())
    if not m:
        driver_error(f"unparsable chainq answer {line.strip()!r} to query {key}")
    if tuple(int(x) for x in m.group(1, 2, 3, 4, 5, 6)) != key:
        driver_error(f"chainq echo {m.group(0)!r} does not match the query {key} "
                     f"that was sent: answers are desynchronised")
    NQ[0] += 1
    return m.group(7) == 'YES'

# The validation range.  DECISIVE = cost <= 16, the deepest cost any consuming
# elimination queries (killer.py's battery tops out at exactly 16 -- measured, not
# assumed); that is the range the paper cites, and it is the default because it
# runs in about two minutes.  The certified table reaches cost REFINED_CMAX = 18,
# and `CMAX=18 python3 qvalid.py` validates all of it; the deeper rows cost
# roughly an hour, because chainq's node counts grow steeply with the cost.
#
# The rule that matters either way: a row the run does NOT validate is COUNTED
# and REPORTED, and a row beyond the certified table depth ABORTS.  A silently
# skipped row is an unvalidated row that the log would still call PASS, which is
# how the previous `if c > CMAX: continue` read.
DECISIVE = 16
TABLE_CMAX = max(r[0] for r in S.REFINED_TABLE)
CMAX = int(os.environ.get('CMAX', DECISIVE))
if CMAX < DECISIVE:
    sys.exit(f"qvalid: CMAX={CMAX} is below the decisive range {DECISIVE}")
if CMAX > TABLE_CMAX:
    sys.exit(f"qvalid: CMAX={CMAX} exceeds the certified table depth {TABLE_CMAX}; "
             f"there is nothing to validate those rows against")
bad = rows = checks = skipped = 0
d_rows = d_checks = d_nq = 0        # the cost <= DECISIVE subtotals
def expect(cond, what, row):
    global bad
    if not cond: print("FAIL", what, row); bad += 1
for row in sorted(S.REFINED_TABLE):
    c, s5, s4 = row[0], row[1], row[2]
    if c > CMAX:
        skipped += 1                     # counted and reported, never silent
        continue
    g00, g10, g01, g11 = row[3:]
    rows += 1
    n0, q0, b0 = checks, NQ[0], bad
    LF = [l for l in (1,2,3,4) if (l == 4 and s5 >= 1) or (l <= 3 and s4 >= 1)]
    gm = max(row[3:])
    if gm >= 0:
        checks += 1
        expect(query(c, s5, s4, 0, 0, gm), "free-yes", row)
        expect(not query(c, s5, s4, 0, 0, gm+1), "free-no", row)
    m10 = max(g10, g11)
    if m10 >= 0:
        checks += 1
        expect(any(query(c, s5, s4, lf, 0, m10) for lf in LF), "first-yes", row)
        expect(not any(query(c, s5, s4, lf, 0, m10+1) for lf in LF), "first-no", row)
    m01 = max(g01, g11)
    if m01 >= 0:
        checks += 1
        expect(any(query(c, s5, s4, 0, lb, m01) for lb in LF), "last-yes", row)
        expect(not any(query(c, s5, s4, 0, lb, m01+1) for lb in LF), "last-no", row)
    if g11 >= 0:
        checks += 1
        expect(any(query(c, s5, s4, lf, lb, g11) for lf in LF for lb in LF),
               "both-yes", row)
        expect(not any(query(c, s5, s4, lf, lb, g11+1) for lf in LF for lb in LF),
               "both-no", row)
    if c <= DECISIVE:
        d_rows += 1; d_checks += checks - n0; d_nq = NQ[0]
    else:
        # One auditable verdict line per row ABOVE the cited decisive range.
        # The CMAX=18 certificate used to be a 16-line summary, so its
        # `0 failures` rested on the author's run alone and could not be checked
        # without repeating the 63-minute job.  Printing the row, its four
        # certified maxima, the queries it consumed and its own failure count
        # makes the claim auditable row by row.
        print(f"ROW c={c:2d} s5={s5:2d} s4={s4:2d}  gS=({g00:3d},{g10:3d},"
              f"{g01:3d},{g11:3d})  checks={checks-n0}  queries={NQ[0]-q0}  "
              f"failures={bad-b0}")
print(f"validated {d_rows} rows (cost <= {DECISIVE}), {d_checks} typed maxima, "
      f"{d_nq} queries, {bad} failures")
if CMAX > DECISIVE:
    print(f"validated cost <= {CMAX}: {rows} rows, {checks} typed maxima, "
          f"{NQ[0]} queries, {bad} failures")
if skipped:
    print(f"certified table depth {TABLE_CMAX}; rows above cost {CMAX} NOT "
          f"validated by this run: {skipped}  (re-run with CMAX={TABLE_CMAX} "
          f"to cover them; about an hour)")
else:
    print(f"certified table depth {TABLE_CMAX}; 0 rows unvalidated -- the whole "
          f"certified refined frontier is covered by this run")
if rows == 0 or checks == 0 or NQ[0] == 0:
    print("QVALID FAIL (nothing was validated)")
    sys.exit(1)
if PROC.poll() not in (None, 0):
    print(f"DRIVER-ERROR: chainq exited rc={PROC.poll()}", file=sys.stderr)
    sys.exit(3)
print("QVALID", "PASS" if bad == 0 else "FAIL")
sys.exit(0 if bad == 0 else 1)
