#!/usr/bin/env python3
"""Compare a fresh 1111-run mysweep sweep against CERTIFICATES/sweep_all.log.

Both logs are written by src/class-elimination/driver.py, whose worker order is
nondeterministic, so the comparison is keyed on each job's TAG (the parameter
string driver.py prints), not on line order.  Verdicts and node counts must both
match; a tag present in one log and absent from the other is a failure.
"""
import re
import sys
from collections import Counter

LINE = re.compile(r'^\[\d+/(\d+)\] (.*?): (SAT|UNSAT) nodes=(\d+) '
                  r'closures=(\d+) phaseQ=(\d+) (EXHAUSTED|CAPPED)\s*$')


def load(path):
    jobs, total, other = {}, None, []
    for n, line in enumerate(open(path), 1):
        line = line.rstrip('\n')
        m = LINE.match(line)
        if not m:
            if line.startswith('['):
                other.append((n, line))
            continue
        total = int(m.group(1))
        tag = m.group(2)
        if tag in jobs:
            sys.exit(f'{path}:{n}: duplicate job tag {tag!r}')
        jobs[tag] = (m.group(3), int(m.group(4)), int(m.group(5)),
                     int(m.group(6)), m.group(7))
    return jobs, total, other


def main():
    fresh_path, committed_path = sys.argv[1], sys.argv[2]
    fresh, ftot, fbad = load(fresh_path)
    comm, ctot, cbad = load(committed_path)
    print(f'  committed {committed_path}: {len(comm)} jobs (header says {ctot})')
    print(f'  fresh     {fresh_path}: {len(fresh)} jobs (header says {ftot})')
    for n, line in fbad + cbad:
        print(f'  UNPARSED [{n}] {line[:110]}')

    only_c = sorted(set(comm) - set(fresh))
    only_f = sorted(set(fresh) - set(comm))
    verdict_diff, node_diff = [], []
    for tag in sorted(set(comm) & set(fresh)):
        c, f = comm[tag], fresh[tag]
        if c[0] != f[0] or c[4] != f[4]:
            verdict_diff.append((tag, c, f))
        elif c[1] != f[1]:
            node_diff.append((tag, c[1], f[1]))

    kinds = Counter((v[0], v[4]) for v in fresh.values())
    print(f'  fresh verdicts     : ' +
          ', '.join(f'{a} {b}={n}' for (a, b), n in sorted(kinds.items())))
    print(f'  fresh node total   : {sum(v[1] for v in fresh.values())}')
    print(f'  committed total    : {sum(v[1] for v in comm.values())}')
    print(f'  jobs only in committed : {len(only_c)}')
    print(f'  jobs only in fresh     : {len(only_f)}')
    print(f'  VERDICT differences    : {len(verdict_diff)}')
    print(f'  NODE-COUNT differences : {len(node_diff)}')
    for t in only_c[:5]:
        print(f'    MISSING FROM FRESH: {t}')
    for t in only_f[:5]:
        print(f'    EXTRA IN FRESH    : {t}')
    for t, c, f in verdict_diff[:10]:
        print(f'    VERDICT {t}: committed {c[0]} {c[4]} / fresh {f[0]} {f[4]}')
    for t, c, f in node_diff[:10]:
        print(f'    NODES   {t}: committed {c} / fresh {f}')

    bad = only_c or only_f or verdict_diff or node_diff or fbad or cbad
    if len(fresh) != 1111 or len(comm) != 1111:
        print('  *** one of the logs does not hold 1111 jobs ***')
        bad = True
    if bad:
        sys.exit('SWEEP COMPARISON FAIL')
    print('\nSWEEP COMPARISON PASS: 1111/1111 jobs agree on verdict AND node '
          'count; 0 SAT, 0 CAPPED')


if __name__ == '__main__':
    main()
