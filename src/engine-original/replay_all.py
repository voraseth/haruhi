#!/usr/bin/env python3
"""replay_all.py -- re-execute the WHOLE 631-job linear campaign of
`src/engine-original/` and compare it node-for-node with the committed logs.

Why this exists.  `run.sh` without arguments only *re-tallies* the eight
committed logs in `CERTIFICATES/campaign-original/`; on a fresh checkout with no
logs it prints `TOTAL: jobs=0`.  The campaign itself was driven by four separate
per-cell drivers (`../class-elimination/mkjobs.py`, `run_z1real.py`,
`run_e9.sh`, `run_e78.sh`), none of which covers all eight logs, so the artifact
shipped no way to re-execute the campaign end to end.  That mattered after the
E-9/E-10 hardening (`INSTFAIL`, `M2SPECFAIL`) changed all four engine sources:
the five committed control cells were re-run, but the other 626 jobs were not.

What it does.  It reads the committed logs as the JOB LIST -- they record every
job's parameters -- reconstructs each job's argv, runs it against freshly built
binaries, and diffs the node count of every job against the committed one.

The field-to-argv mapping is taken from the drivers' own source, not guessed:

  realize2  n5 n4 n3 n2 n1 ncyc s2list bq1 [cap]
      mkjobs.py:run() builds exactly
          [eng, n5, n4, n3, n2, n1, c1, s2s, bq1] + ([X4h] if X4h) + [cap]
      with eng = 'realize2' if X4h == 0 else 'realize3', and prints
          "n5=.. n4=.. S=(Nx3,Nx2,Nx1) c1=.. s2=.. bq1=.."
      so the printed fields ARE the argv, in order; `s2` is the s2list verbatim
      (`','.join(s2v)` or `'0'`), and `ncyc` is the printed `c1`.
  realize3  ... s2list bq1 nd4 [cap]        nd4 = the X4h of the section header.
  realize4  n5 n4 n3 n2 n1 ncyc s2list bq1 bmode blen [cap]
      run_z1real.py builds [eng, n5, n4, n3, n2, n1, '0', sA, '0', mode, lB, cap]
      and prints "n5=.. n4=.. S=(..) sA=.. lB=..", with mode 1 = zh, 2 = zp3
      taken from the section header.
  realize   n5 n4 n3 n2 n1 ncyc m2spec [cap]
      run_e9.sh and run_e78.sh hold these eleven jobs as literal command lines
      with two-digit l1l2 M2 tokens, which the log's label lines do NOT record
      (the log prints "job1 n5=16 shorts(3,3) s2=2", not the m2spec).  So for
      those two logs the argv is parsed out of the SHELL SCRIPTS themselves and
      matched to the log by its echoed label, which is checked to agree.

Self-check before anything runs: every `N jobs` count in every section header
must equal the number of jobs parsed for that section, every log's job count
must equal its number of verdict lines, and the total must be 631.  Any line
that does not parse is fatal -- a silently skipped job would shrink the campaign.

Exit conventions (read from the engine sources, not assumed): realize/2/3/4
return 0 on SAT, 2 on `UNSAT ... EXHAUSTED`, 3 on `NODE_CAP_HIT` and on the
`INSTFAIL`/`M2SPECFAIL` instance guards, 1 on a usage error.  A job counts as
reproduced only when the child exited 2 with the `UNSAT ... EXHAUSTED` marker
AND its node count equals the committed one.

    python3 replay_all.py                 # build, self-check, run all 631
    python3 replay_all.py --check-only    # parse and self-check, run nothing
    python3 replay_all.py -j 4            # 4 workers (default: cpu_count)
"""
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir, os.pardir))
LOGDIR = os.path.join(ROOT, 'CERTIFICATES', 'campaign-original')
CAP = '4000000000'          # the cap every committed driver used

# ---------------------------------------------------------------- log parsing
HDR_CELL = re.compile(r'^== \((\d+),(\d+),(\d+)\) e=(\d+)(?: X4h=(\d+))?: (\d+) jobs ==')
HDR_Z1 = re.compile(r'^== \(15,0,1\) e=2, (zh|zp3) wiring: (\d+) jobs ==')
JOB_CELL = re.compile(
    r'^\s*n5=(\d+) n4=(\d+) S=\((\d+)x3,(\d+)x2,(\d+)x1\) '
    r'c1=(\d+) s2=([\d,]+) bq1=(\d+): (.*)$')
JOB_Z1 = re.compile(
    r'^\s*n5=(\d+) n4=(\d+) S=\((\d+)x3,(\d+)x2,(\d+)x1\) '
    r'sA=(\d+) lB=(\d+): (.*)$')
VERDICT = re.compile(r'\b(SAT|UNSAT) nodes=(\d+)\b')
SUMMARY = re.compile(r'^\s*-->|^\s*deepest trace|^\s+[QAM] head=')
SH_JOB = re.compile(r'^echo "([^"]*)";\s*\$R((?: +[\w,]+)+) \$C\s*$')


def fail(msg):
    sys.exit('replay_all: ' + msg)


def parse_cell_log(path, engine_for_x4h):
    """logs whose jobs mkjobs.py drove: realize2 (X4h=0) or realize3 (X4h>0)."""
    jobs, sect, want = [], None, None
    for n, line in enumerate(open(path), 1):
        line = line.rstrip('\n')
        if not line.strip() or SUMMARY.match(line):
            continue
        h = HDR_CELL.match(line)
        if h:
            if sect is not None and want != sect['got']:
                fail(f'{path}:{n}: previous section declared {want} jobs, '
                     f'{sect["got"]} parsed')
            x4h = int(h.group(5) or 0)
            sect = {'x4h': x4h, 'got': 0}
            want = int(h.group(6))
            continue
        m = JOB_CELL.match(line)
        if not m:
            fail(f'{path}:{n}: unparseable line {line!r}')
        if sect is None:
            fail(f'{path}:{n}: job line before any section header')
        v = VERDICT.search(m.group(9))
        if not v:
            fail(f'{path}:{n}: job line carries no verdict: {line!r}')
        n5, n4, n3, n2, n1, c1, s2, bq1 = m.group(1, 2, 3, 4, 5, 6, 7, 8)
        x4h = sect['x4h']
        eng = 'realize2' if x4h == 0 else 'realize3'
        argv = [n5, n4, n3, n2, n1, c1, s2, bq1]
        if x4h:
            argv.append(str(x4h))
        argv.append(CAP)
        jobs.append((os.path.basename(path), n, eng, argv,
                     v.group(1), int(v.group(2)), line))
        sect['got'] += 1
    if sect is not None and want != sect['got']:
        fail(f'{path}: last section declared {want} jobs, {sect["got"]} parsed')
    return jobs


def parse_z1_log(path):
    """realize_z1.log: run_z1real.py drove these with realize4."""
    jobs, mode, want, got = [], None, None, 0
    for n, line in enumerate(open(path), 1):
        line = line.rstrip('\n')
        if not line.strip() or SUMMARY.match(line):
            continue
        h = HDR_Z1.match(line)
        if h:
            if mode is not None and want != got:
                fail(f'{path}:{n}: section declared {want} jobs, {got} parsed')
            mode = '1' if h.group(1) == 'zh' else '2'
            want, got = int(h.group(2)), 0
            continue
        m = JOB_Z1.match(line)
        if not m:
            fail(f'{path}:{n}: unparseable line {line!r}')
        if mode is None:
            fail(f'{path}:{n}: job line before any wiring header')
        v = VERDICT.search(m.group(8))
        if not v:
            fail(f'{path}:{n}: job line carries no verdict: {line!r}')
        n5, n4, n3, n2, n1, sA, lB = m.group(1, 2, 3, 4, 5, 6, 7)
        argv = [n5, n4, n3, n2, n1, '0', sA, '0', mode, lB, CAP]
        jobs.append((os.path.basename(path), n, 'realize4', argv,
                     v.group(1), int(v.group(2)), line))
        got += 1
    if mode is not None and want != got:
        fail(f'{path}: last section declared {want} jobs, {got} parsed')
    return jobs


def parse_shell_driven(logpath, shpath):
    """realize_e9.log / realize_e78.log: the m2spec lives only in the script."""
    script = []
    for line in open(shpath):
        m = SH_JOB.match(line.strip())
        if m:
            script.append((m.group(1), m.group(2).split()))
    if not script:
        fail(f'{shpath}: no `echo "..."; $R ... $C` job lines found')
    jobs, i = [], 0
    pending_label = None
    for n, line in enumerate(open(logpath), 1):
        line = line.rstrip('\n')
        if not line.strip() or SUMMARY.match(line):
            continue
        if line.startswith('=='):
            continue
        v = VERDICT.search(line)
        if v:
            if pending_label is None:
                fail(f'{logpath}:{n}: verdict with no preceding label line')
            if i >= len(script):
                fail(f'{logpath}:{n}: more verdicts than {shpath} has jobs')
            label, args = script[i]
            if label != pending_label:
                fail(f'{logpath}:{n}: log label {pending_label!r} does not match '
                     f'{shpath} job {i + 1} label {label!r}')
            jobs.append((os.path.basename(logpath), n, 'realize',
                         args + [CAP], v.group(1), int(v.group(2)), line))
            i += 1
            pending_label = None
            continue
        pending_label = line.strip()
    if i != len(script):
        fail(f'{logpath}: {i} verdicts but {shpath} declares {len(script)} jobs')
    return jobs


def build_joblist():
    jobs = []
    for name in ('realize_c10.log', 'realize_c15.log', 'realize_e321.log',
                 'realize_e54.log', 'realize_e6.log'):
        jobs += parse_cell_log(os.path.join(LOGDIR, name), True)
    jobs += parse_z1_log(os.path.join(LOGDIR, 'realize_z1.log'))
    jobs += parse_shell_driven(os.path.join(LOGDIR, 'realize_e9.log'),
                               os.path.join(HERE, 'run_e9.sh'))
    jobs += parse_shell_driven(os.path.join(LOGDIR, 'realize_e78.log'),
                               os.path.join(HERE, 'run_e78.sh'))
    return jobs


# ------------------------------------------------------------------- running
def classify(rc, line):
    """realize*: 0 = SAT, 2 = UNSAT (exhausted), 3 = cap / INSTFAIL /
    M2SPECFAIL, 1 = usage.  A negative verdict needs BOTH the exit status and
    the completion marker."""
    if line.startswith('UNSAT ') and 'EXHAUSTED' in line and rc == 2:
        return 'UNSAT'
    if line.startswith('SAT ') and rc == 0:
        return 'SAT'
    if ('NODE_CAP_HIT' in line or 'CAPPED' in line) and rc == 3:
        return 'CAPPED'
    if ('INSTFAIL' in line or 'M2SPECFAIL' in line) and rc == 3:
        return 'INSTFAIL'
    return 'DRIVER-ERROR'


def run_one(job):
    log, lineno, eng, argv, want_verdict, want_nodes, src = job
    cmd = [os.path.join(HERE, eng)] + argv
    r = subprocess.run(cmd, capture_output=True, text=True)
    out = r.stdout.splitlines()[0] if r.stdout else f'ENGINE ERROR rc={r.returncode}'
    kind = classify(r.returncode, out)
    v = VERDICT.search(out)
    got_nodes = int(v.group(2)) if v else None
    ok = (kind == want_verdict and got_nodes == want_nodes)
    return (job, cmd, r.returncode, out, kind, got_nodes, ok)


def main():
    args = sys.argv[1:]
    check_only = '--check-only' in args
    workers = os.cpu_count() or 4
    if '-j' in args:
        workers = int(args[args.index('-j') + 1])

    jobs = build_joblist()
    from collections import Counter
    per_log = Counter(j[0] for j in jobs)
    per_eng = Counter(j[2] for j in jobs)
    print('== self-check: job list reconstructed from the committed logs ==')
    for name in sorted(per_log):
        path = os.path.join(LOGDIR, name)
        verdicts = sum(1 for ln in open(path) if VERDICT.search(ln))
        flag = 'OK ' if verdicts == per_log[name] else 'MISMATCH'
        print(f'  {flag} {name:<20} {per_log[name]:>4} jobs parsed, '
              f'{verdicts:>4} verdict lines in the log')
        if verdicts != per_log[name]:
            fail(f'{name}: parsed {per_log[name]} jobs but the log has '
                 f'{verdicts} verdict lines')
    print(f'  by engine: ' + ', '.join(f'{k}={v}' for k, v in sorted(per_eng.items())))
    print(f'  TOTAL {len(jobs)} jobs')
    if len(jobs) != 631:
        fail(f'expected 631 jobs, reconstructed {len(jobs)}')
    print('  SELF-CHECK PASS: 631 jobs, every section count matches its header\n')
    if check_only:
        return

    for eng in sorted(per_eng):
        exe = os.path.join(HERE, eng)
        src = os.path.join(HERE, eng + '.c')
        if subprocess.run(['cc', '-O2', '-o', exe, src]).returncode:
            fail(f'failed to build {eng}')
    print(f'built {len(per_eng)} engines; running {len(jobs)} jobs '
          f'on {workers} workers\n')

    results = []
    done = [0]
    import threading
    lock = threading.Lock()

    def work(j):
        res = run_one(j)
        with lock:
            done[0] += 1
            results.append(res)
            if not res[6] or done[0] % 50 == 0:
                job, cmd, rc, out, kind, got, ok = res
                print(f'[{done[0]}/{len(jobs)}] {job[0]}:{job[1]} '
                      f'{"OK " if ok else "MISMATCH"} {os.path.basename(cmd[0])} '
                      f'{" ".join(cmd[1:])} -> {out}', flush=True)
    with ThreadPoolExecutor(max_workers=workers) as ex:
        list(ex.map(work, jobs))

    bad = [r for r in results if not r[6]]
    total = sum(r[5] for r in results if r[5] is not None)
    kinds = Counter(r[4] for r in results)
    print('\n== replay result ==')
    print(f'  jobs replayed      : {len(results)}')
    print(f'  verdicts           : ' + ', '.join(f'{k}={v}' for k, v in sorted(kinds.items())))
    print(f'  node total         : {total}')
    print(f'  committed total    : 10993460947')
    print(f'  node mismatches    : {len(bad)}')
    for job, cmd, rc, out, kind, got, ok in bad:
        print(f'  MISMATCH {job[0]}:{job[1]}')
        print(f'    committed: {job[4]} nodes={job[5]}')
        print(f'    replay   : {kind} nodes={got} rc={rc}  ({out})')
        print(f'    command  : {" ".join(cmd)}')
    if bad or total != 10993460947 or kinds.get('UNSAT') != 631:
        sys.exit('REPLAY FAIL: the post-edit binaries do not reproduce the '
                 'committed campaign')
    print('\nREPLAY PASS: all 631 jobs UNSAT EXHAUSTED, node-identical to '
          'CERTIFICATES/campaign-original/, total 1.099e10')


if __name__ == '__main__':
    main()
