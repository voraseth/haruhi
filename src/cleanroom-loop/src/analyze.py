#!/usr/bin/env python3
"""Structural analyzer written from Section 'Preliminaries' / 'First-occurrence
structure' of PAPER-n6-872-v2.tex.  Reproduces the printed profile of a
superpermutation: runs, e, P, link-path lengths, D, transitions, pointer
components, chains.  Used as an implementation-independent invariant control."""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("analyze: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 4 `assert` statements")
import sys
from itertools import permutations

W = ''.join(sys.argv[1:2]) or 'data/w872.txt'
S = open(W).read().strip()

PERMS = [''.join(p) for p in permutations('123456')]
IDX = {p: i for i, p in enumerate(PERMS)}
rot = lambda p: p[1:] + p[0]
sig = lambda p: p[2:] + p[1] + p[0]
rho = lambda p: p[1:5] + p[0] + p[5]


def d(p, q):
    assert p != q
    for k in range(5, 0, -1):
        if p[6 - k:] == q[:k]:
            return 6 - k
    return 6


# ---- first-occurrence ordering
seen, order = set(), []
for i in range(len(S) - 5):
    w = S[i:i + 6]
    if w in IDX and w not in seen:
        seen.add(w); order.append(w)
assert len(order) == 720, len(order)
cost = [d(order[k], order[k + 1]) for k in range(719)]

# ---- runs
runs = []            # list of lists of permutations
cur = [order[0]]
for k in range(719):
    if cost[k] == 1:
        assert order[k + 1] == rot(order[k])
        cur.append(order[k + 1])
    else:
        runs.append(cur); cur = [order[k + 1]]
runs.append(cur)
nruns = len(runs)
e = nruns - 120

# ---- classes, criticals
cls = {}
reps = []
for p in PERMS:
    if p not in cls:
        c = len(reps); reps.append(p)
        q = p
        for _ in range(6):
            cls[q] = c; q = rot(q)
assert len(reps) == 120
last = {}
for i, p in enumerate(order):
    last[cls[p]] = p
crit = {c: rot(last[c]) for c in range(120)}
critset = set(crit.values())
runstart = [r[0] for r in runs]
runof = {}
for i, r in enumerate(runs):
    for p in r:
        runof[p] = i
iscrit = [runstart[i] in critset for i in range(nruns)]
ncrit = sum(iscrit)

# ---- links and link-paths
# a cost-2 exit from a completion y_C lands on sig(y_C); it is a link if that
# landing is the critical permutation of its class.
link_from = {}
for k in range(719):
    z = order[k]
    if cost[k] == 2 and z == last[cls[z]]:
        t = order[k + 1]
        if t == sig(z) and t in critset:
            link_from[cls[z]] = cls[t]
succ = link_from
pred = {v: k for k, v in succ.items()}
paths = []
for c in range(120):
    if c in pred:
        continue
    p = [c]
    while p[-1] in succ:
        p.append(succ[p[-1]])
    paths.append(p)
P = len(paths)
D = sum(5 - len(p) for p in paths)
lens = {}
for p in paths:
    lens[len(p)] = lens.get(len(p), 0) + 1

# ---- pointer graph: arc per cost-2 transition, from run(rot(z)) to run(landing)
arcs = []
for k in range(719):
    if cost[k] == 2:
        z = order[k]
        arcs.append((runof[rot(z)], runof[order[k + 1]]))
outd, ind = {}, {}
for a, b in arcs:
    outd.setdefault(a, []).append(b); ind.setdefault(b, []).append(a)
# check the rho-advance claimed in the paper
bad = sum(1 for a, b in arcs if runstart[b] != rho(runstart[a]))

# components
seenv, comps = set(), []
adj = {}
for a, b in arcs:
    adj.setdefault(a, set()).add(b); adj.setdefault(b, set()).add(a)
for v in range(nruns):
    if v in seenv:
        continue
    st, comp = [v], []
    seenv.add(v)
    while st:
        u = st.pop(); comp.append(u)
        for w in adj.get(u, ()):
            if w not in seenv:
                seenv.add(w); st.append(w)
    comps.append(comp)
ncyc = sum(1 for comp in comps
           if all(len(outd.get(v, [])) == 1 for v in comp))
cyc_sizes = sorted(set(len(comp) for comp in comps
                       if all(len(outd.get(v, [])) == 1 for v in comp)))

# ---- transitions by cost
from collections import Counter
cc = Counter(cost)
X4 = sum((c - 3) for c in cost if c >= 4)
X4h = sum(1 for c in cost if c >= 4)
waste = sum(c - 1 for c in cost)
nch = P - cc.get(3, 0)

print("length            %d" % len(S))
print("runs              %d   (e = %d)" % (nruns, e))
print("critical runs     %d" % ncrit)
print("link-paths P      %d   lengths %s   D = %d" % (P, dict(sorted(lens.items())), D))
print("cost histogram    %s" % dict(sorted(cc.items())))
print("waste             %d   X4 = %d  X4h = %d" % (waste, X4, X4h))
print("pointer comps     %d  (cycles %d, cycle sizes %s)" % (len(comps), ncyc, cyc_sizes))
print("chains ch         %d   (= P - #cost3)" % nch)
print("rho-advance violations among pointer arcs: %d / %d" % (bad, len(arcs)))
print("identity P=24+D/5 : %s ; waste=142+D/5+X4+Z : %d" % (P == 24 + D // 5, 142 + D // 5 + X4))
