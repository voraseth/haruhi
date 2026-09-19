#!/usr/bin/env python3
"""itemA control check: compute the Lemma-3.4 profile variables from raw
n=6 definitions for each control superpermutation and verify inequalities
(i)-(vi). Independent reimplementation (not derived from bounds/checks/).

Definitions (raw):
  perms = all 720 orderings; first-occurrence ordering q_1..q_720 by window
  position; w_i = d(q_i,q_{i+1}) = 6 - overlap; runs = maximal weight-1
  segments; sigma = left rotation; rho(p) = p2..p5 p1 p6; tau(p) = p3..p6 p2 p1.
  Pointer graph: vertex per run; per T-type transition (w=2, target=tau(end)),
  edge run(sigma(end)) -> run(target).
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("itemA_control_check: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 14 `assert` statements")
import sys, itertools, glob

N = 6
def sigma(p): return p[1:] + p[:1]
def rho(p):   return p[1:N-1] + p[:1] + p[N-1:]
def tau(p):   return p[2:] + p[1] + p[0]

def d(p, q):
    for ov in range(N-1, -1, -1):
        if p[N-ov:] == q[:ov]:
            return N - ov
    return N

def profile(s):
    # first-occurrence ordering
    seen, order = set(), []
    for i in range(len(s) - N + 1):
        w = s[i:i+N]
        if len(set(w)) == N and w not in seen:
            seen.add(w); order.append(w)
    assert len(order) == 720, f"only {len(order)} perms"
    w = [d(order[i], order[i+1]) for i in range(719)]

    # runs: maximal weight-1 segments; run i covers order[a..b]
    runs = []; a = 0
    for i in range(719):
        if w[i] != 1:
            runs.append((a, i)); a = i + 1
    runs.append((a, 719))
    m = len(runs)
    start = {j: order[a] for j, (a, b) in enumerate(runs)}
    startrun = {order[a]: j for j, (a, b) in enumerate(runs)}
    full = {j: (b - a + 1 == N) for j, (a, b) in enumerate(runs)}
    # sanity: run inside one 1-cycle, steps are sigma
    for j,(a,b) in enumerate(runs):
        for i in range(a,b): assert order[i+1] == sigma(order[i])
        assert b - a + 1 <= N

    # 1-cycle classes: canonical rep = min rotation
    def cls(p): return min(p[i:] + p[:i] for i in range(N))
    kC = {}
    for j,(a,b) in enumerate(runs):
        kC[cls(order[a])] = kC.get(cls(order[a]), 0) + 1
    extra = sum(k-1 for k in kC.values()); assert m == 120 + extra
    e3 = sum(k-1 for k in kC.values() if k >= 3)
    d2 = sum(1 for k in kC.values() if k == 2)
    dirty = sum(1 for k in kC.values() if k >= 2)
    F = sum(1 for j in full if not full[j]); assert F == extra + dirty

    # transitions
    alpha = 0; Q2 = 0; h = 0; edges = []
    for t in range(m - 1):
        aa, bb = runs[t]; e = order[bb]; tgt = start[t+1]; wt = w[bb]
        assert wt >= 2
        if wt >= 3:
            alpha += 1; h += wt - 3
        else:
            if tgt == sigma(sigma(e)): Q2 += 1
            else:
                assert tgt == tau(e)
                src = startrun[sigma(e)]           # (O2): sigma(end) is a run start
                dst = startrun[tgt]                # (O1)
                edges.append((src, dst))
    # pointer graph components
    P2 = len(edges); assert P2 + Q2 + alpha == m - 1
    out = {}; inn = {}
    for s_, t_ in edges:
        assert s_ not in out and t_ not in inn
        out[s_] = t_; inn[t_] = s_
    Ncyc = 0; PT = 0; comp_seen = set()
    for j in range(m):
        if j in comp_seen: continue
        if j in inn and j not in comp_seen:
            # find if j is on a cycle or find chain head
            pass
    # walk components properly
    heads = [j for j in range(m) if j not in inn]
    nchains = 0
    for hd in heads:
        comp = [hd]; cur = hd
        while cur in out:
            cur = out[cur]; comp.append(cur)
        comp_seen.update(comp); nchains += 1
        if len(comp) == N - 1 and all(full[r] for r in comp): PT += 1
        assert len(comp) <= N - 1
        for i in range(len(comp)-1):
            assert start[comp[i+1]] == rho(start[comp[i]])
    for j in range(m):
        if j not in comp_seen:      # cycle component
            comp = [j]; cur = out[j]
            while cur != j: comp.append(cur); cur = out[cur]
            comp_seen.update(comp); Ncyc += 1
            assert len(comp) == N - 1   # cycles have size exactly n-1
    assert nchains == 1 + Q2 + alpha, (nchains, Q2, alpha)

    Delta = (N-1) * (1 + alpha + Q2 + Ncyc) - m
    t_ = extra + alpha + h
    cost = sum(w)
    assert cost == 720 + 120 - 2 + t_
    return dict(L=len(s.strip()), m=m, extra=extra, e3=e3, d2=d2, dirty=dirty,
                F=F, Q2=Q2, Ncyc=Ncyc, alpha=alpha, h=h, Delta=Delta, PT=PT, t=t_)

def check_ineqs(v):
    fails = []
    if not (v['Q2'] + v['Ncyc'] <= v['extra']): fails.append('(i)')
    if not (v['Q2'] <= v['e3']):                fails.append('(ii)')
    if not (v['Delta'] >= 0):                   fails.append('(iii)')
    if not (v['PT'] >= 1 + v['alpha'] + v['Q2'] - v['Delta'] - (v['F'] - v['Ncyc'])):
        fails.append('(iv)')
    if not (v['PT'] <= v['m'] // 5):            fails.append('(v)')
    if not (5*v['PT'] <= 4*(2 + v['h'] + v['alpha'] + v['F'])): fails.append('(vi)')
    if not (v['dirty'] <= v['d2'] + v['e3']//2): fails.append('(dirty-cap)')
    return fails

# --- repository-portable path setup (added when vendoring into the public
# repository; the audit workspace originals resolved these against the
# project tree).  LIB holds lib6.py / scan871.py / validate871.py; DATA holds
# best872.txt and optimal-873/sol*.txt. ---
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
LIB  = _os.path.join(_HERE, _os.pardir, 'lib')
DATA = _os.path.abspath(_os.path.join(_HERE, _os.pardir, _os.pardir, _os.pardir, 'data'))
_sys.path.insert(0, LIB)
P872 = _os.environ.get('SUPERPERM_P872') or _os.path.join(DATA, 'best872.txt')
# SUPERPERM_P872 substitutes another length-872 witness in the 872 slot of
# the control corpus; see ../../external-872-control/.
G873 = _os.path.join(DATA, 'optimal-873', 'sol*.txt')
# --- end path setup ---
files = [P872] + sorted(glob.glob(G873))
if len(files) != 97:
    sys.exit(f"corpus: expected 97 objects (1 x 872 + 96 x 873), found {len(files)}")
bad = 0
for i, fn in enumerate(files):
    s = open(fn).read().strip()
    v = profile(s)
    fl = check_ineqs(v)
    tag = fn.split('/')[-1]
    if fl or i == 0 or i == 1:
        print(tag, v, 'FAILS:' if fl else 'OK', fl if fl else '')
    if fl: bad += 1
print(f"checked {len(files)} sequences; {bad} violations")
sys.exit(1 if bad else 0)
