#!/usr/bin/env python3
"""verify_e0_873.py -- the POSITIVE CONTROL for the ordering search.

    python3 verify_e0_873.py out/E0_873_S24_X6.txt

`e9exact` is the one decisive searcher of this repository whose production
verdict is "solutions=0": at L = 871, e = 0 it exhausts nine instances and finds
nothing.  A searcher that can only reject proves nothing by rejecting, so it has
to be shown finding something.  At L = 873 with e = 0 it must find the known
optimal orderings and no others: all 96 objects of data/optimal-873/ have
e = 0, D = 0, X4 = 6, and L = 843 + E + S + X4 forces S = 24, so the single
instance (E,S,X4) = (0,24,6) is exactly their habitat.

This script reads that run's output, reconstructs a superpermutation string from
each emitted ordering, and checks it from the raw definitions:

  * a run is a maximal weight-1 segment, so run i is the perms
    rs, rot(rs), ..., rot^(rl-1)(rs) with rot(p) = p2..p6 p1;
  * rj[i] is the weight of the join INTO run i (rj[0] = 0);
  * the string starts with the 6 characters of the first permutation and each
    later permutation contributes its last w characters, w being its transition
    weight;
  * so |string| = 6 + sum of all 719 weights, and each of the 720 permutations
    must appear as a window.

It then confirms every reconstructed string is a length-873 superpermutation
(independently, by counting windows) and that the emitted set is exactly the 96
known ones up to the relabelling the search takes WLOG.

Exit 0 iff the run EXHAUSTED, emitted exactly 96 solutions, and every one
reconstructs to a valid length-873 superpermutation.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("verify_e0_873: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import itertools
import os
import sys


HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir, os.pardir))

PERMS = [''.join(p) for p in itertools.permutations('123456')]   # lexicographic
IDX = {p: i for i, p in enumerate(PERMS)}
ROT = [IDX[p[1:] + p[0]] for p in PERMS]                         # rot(p)=p2..p6 p1


def d(p, q):
    """the transition weight: 6 minus the longest suffix of p that prefixes q."""
    for k in range(1, 6):
        if p[k:] == q[:6 - k]:
            return k
    return 6


def windows(s):
    return {s[i:i+6] for i in range(len(s) - 5) if len(set(s[i:i+6])) == 6}


def parse(path):
    """-> (header, [[(rs, rl, rj), ...], ...], tail)"""
    sols, cur, header, tail = [], None, None, None
    for line in open(path):
        line = line.strip()
        if line.startswith('E='):
            header = line
        elif line.startswith('SOL'):
            cur = []
        elif line.startswith('RUN'):
            _, a, b, c = line.split()
            cur.append((int(a), int(b), int(c)))
        elif line == 'ENDSOL':
            sols.append(cur)
            cur = None
        elif line.startswith('nodes='):
            tail = line
    return header, sols, tail


def rebuild(runs):
    """the ordering, then the string, both from the definitions."""
    order, weights = [], []
    for i, (rs, rl, rj) in enumerate(runs):
        p = rs
        for j in range(rl):
            order.append(p)
            weights.append(1 if j else (rj if i else 0))
            p = ROT[p]
    s = PERMS[order[0]]
    for k in range(1, len(order)):
        q = PERMS[order[k]]
        w = weights[k]
        if w != d(PERMS[order[k-1]], q):
            return None, f"run-list weight {w} != d = {d(PERMS[order[k-1]], q)} at {k}"
        s += q[6 - w:]
    return s, None


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        HERE, 'out', 'E0_873_S24_X6.txt')
    header, sols, tail = parse(path)
    print(f"run: {header}")
    print(f"tail: {tail}")
    fail = 0

    def check(name, ok, extra=''):
        nonlocal fail
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}{(' :: ' + extra) if extra else ''}")
        if not ok:
            fail += 1

    check("the run EXHAUSTED (not capped)", tail is not None and
          'EXHAUSTED' in tail and 'NODE_CAP_HIT' not in tail, str(tail))
    check("exactly 96 solutions emitted", len(sols) == 96, str(len(sols)))
    check("every solution has 120 runs (R = 120 + E, E = 0)",
          all(len(r) == 120 for r in sols),
          str(sorted({len(r) for r in sols})))

    strings, bad = [], []
    for i, runs in enumerate(sols):
        s, err = rebuild(runs)
        if err:
            bad.append((i, err))
            continue
        if len(s) != 873:
            bad.append((i, f"length {len(s)} != 873"))
            continue
        w = windows(s)
        if len(w) != 720:
            bad.append((i, f"only {len(w)} of 720 permutations occur"))
            continue
        strings.append(s)
    check("every solution reconstructs to a length-873 SUPERPERMUTATION "
          "(720/720 windows, weights re-derived from d)",
          not bad and len(strings) == 96,
          f"{len(strings)} valid, {len(bad)} bad: {bad[:3]}")
    check("the 96 reconstructed strings are distinct", len(set(strings)) == 96,
          str(len(set(strings))))

    # -- and they are the known ones, up to the relabelling the search fixes WLOG
    known = []
    d873 = os.path.join(ROOT, 'data', 'optimal-873')
    for fn in sorted(os.listdir(d873)):
        if fn.endswith('.txt'):
            known.append(open(os.path.join(d873, fn)).read().strip())
    check("data/optimal-873/ holds 96 objects", len(known) == 96, str(len(known)))

    def canon(s):
        """relabel so the first window is 123456: the search fixes q1 WLOG."""
        first = s[:6]
        m = {c: str(i + 1) for i, c in enumerate(first)}
        return ''.join(m[c] for c in s)

    ck, cs = {canon(x) for x in known}, {canon(x) for x in strings}
    check("the emitted set EQUALS the 96 known objects, up to relabelling",
          ck == cs, f"only-known={len(ck - cs)} only-found={len(cs - ck)}")

    if strings:
        print(f"\n  first reconstructed string (truncated): {strings[0][:72]}...")
    print(f"\n{'E0-873 CALIBRATION PASS' if fail == 0 else f'{fail} CHECKS FAILED'}")
    sys.exit(1 if fail else 0)


if __name__ == '__main__':
    main()
