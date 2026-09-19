
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("realize_check: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 3 `assert` statements")
#!/usr/bin/env python3
# realize_check.py -- INDEPENDENT re-implementation of the stage-2 model of
# checks/realize.c (no shared code or tables; d from the raw definition;
# strings and sets, not bitmask indices).  Cross-validation of the e=9 kill.
import sys
from itertools import permutations

def rho(p): return p[1:5] + p[0] + p[5]
def rot(p): return p[1:] + p[:1]
def rotinv(p): return p[-1] + p[:-1]
def cls(p):
    b = p; q = p
    for _ in range(5):
        q = rot(q)
        if q < b: b = q
    return b
def dist(p, q):
    for k in range(1, 7):
        if p[k:] == q[:6-k]: return k
    return 6

perms = [''.join(x) for x in permutations('123456')]
# d=3 successors from the raw definition (must be exactly 6 each)
hop = {p: [q for q in perms if dist(p, q) == 3] for p in perms}
assert all(len(v) == 6 for v in hop.values())
hop4 = {p: [q for q in perms if dist(p, q) == 4] for p in perms}
assert all(len(v) == 24 for v in hop4.values())
orbit_of = {}
orbits = []
for p in perms:
    if p in orbit_of: continue
    o = [p]; q = rho(p)
    while q != p: o.append(q); q = rho(q)
    oi = len(orbits)
    for x in o: orbit_of[x] = oi
    orbits.append(o)

class State:
    def __init__(s):
        s.covered = set()       # classes covered as crits
        s.usedperm = set()      # perms used as run starts
        s.nodes = 0

def place_arc(s, x, l):
    ps, cs = [], []
    q = x
    for _ in range(l):
        c = cls(q)
        if q in s.usedperm or c in s.covered: return None
        ps.append(q); cs.append(c); q = rho(q)
    if len(set(cs)) != l: return None
    for q2, c2 in zip(ps, cs): s.usedperm.add(q2); s.covered.add(c2)
    return (ps, cs)
def unplace(s, rec):
    ps, cs = rec
    for q2 in ps: s.usedperm.discard(q2)
    for c2 in cs: s.covered.discard(c2)

def arc_end(x, l):
    q = x
    for _ in range(l - 1): q = rho(q)
    return rotinv(q)

def solve(n5, n4, shorts, ncyc, m2opts, chainonly=False, cap=10**9, nd4=0):
    rem = {5: n5, 4: n4}
    for l in shorts: rem[l] = rem.get(l, 0) + 1
    s = State()
    def endgame():
        # node counting convention matched to realize.c: the dfs-level entry is
        # counted once, inside eg(); chainonly short-circuits without a count.
        if chainonly: return True
        # cover remaining classes with ncyc full virgin orbits (4 crits + nc)
        def eg(k):
            s.nodes += 1
            unc = [c for c in (cls(p) for p in perms) ]  # not used; find below
            uncov = None
            for oi, o in enumerate(orbits): pass
            # lowest uncovered class:
            allcls = sorted({cls(p) for p in perms})
            low = next((c for c in allcls if c not in s.covered), None)
            if low is None: return k == 0
            if k == 0: return False
            for p in perms:
                if cls(p) != low: continue
                oi = orbit_of[p]
                o = orbits[oi]
                if any(q in s.usedperm for q in o): continue
                pc = o.index(p)
                for nc in range(5):
                    if nc == pc: continue
                    crits = [o[j] for j in range(5) if j != nc]
                    if any(cls(q) in s.covered for q in crits): continue
                    for q in o: s.usedperm.add(q)
                    for q in crits: s.covered.add(cls(q))
                    if eg(k - 1): return True
                    for q in crits: s.covered.discard(cls(q))
                    for q in o: s.usedperm.discard(q)
            return False
        return eg(ncyc)
    def dfsA(end, m2placed):
        return dfsQ(end)
    m2left = [1 if m2opts else 0]
    def m2opts_left(): return m2left[0] > 0
    d4rem = [nd4]
    def dfsQ(end):
        s.nodes += 1
        if s.nodes > cap: raise TimeoutError
        if not m2opts_left() and d4rem[0] == 0 and all(v == 0 for v in rem.values()):
            return endgame()
        for t in hop[end]:
            for l in sorted(rem, reverse=True):
                if rem[l] == 0: continue
                r = place_arc(s, t, l)
                if r is None: continue
                rem[l] -= 1
                if dfsQ(arc_end(t, l)): return True
                rem[l] += 1
                unplace(s, r)
            # close with M2
            for (l1, l2) in (m2opts if m2opts_left() else []):
                span = l1 + 1 + l2
                q = t; ps = []; crits = []
                ok = True
                for j in range(span):
                    if q in s.usedperm: ok = False; break
                    if j != l1 and cls(q) in s.covered: ok = False; break
                    ps.append((j, q)); q = rho(q)
                if not ok or len({q for _, q in ps}) != span: continue
                for j, q2 in ps:
                    s.usedperm.add(q2)
                    if j != l1: s.covered.add(cls(q2))
                k2h = ps[l1 + 1][1]
                m2left[0] -= 1
                if dfsA(arc_end(k2h, l2), True): m2left[0] += 1; return True
                m2left[0] += 1
                for j, q2 in ps:
                    s.usedperm.discard(q2)
                    if j != l1: s.covered.discard(cls(q2))
        if d4rem[0] > 0:
            for t in hop4[end]:
                for l in sorted(rem, reverse=True):
                    if rem[l] == 0: continue
                    r = place_arc(s, t, l)
                    if r is None: continue
                    rem[l] -= 1; d4rem[0] -= 1
                    if dfsQ(arc_end(t, l)): return True
                    d4rem[0] += 1; rem[l] += 1
                    unplace(s, r)
                for (l1, l2) in (m2opts if m2opts_left() else []):
                    span = l1 + 1 + l2
                    q = t; ps = []; ok = True
                    for j in range(span):
                        if q in s.usedperm: ok = False; break
                        if j != l1 and cls(q) in s.covered: ok = False; break
                        ps.append((j, q)); q = rho(q)
                    if not ok or len({q2 for _, q2 in ps}) != span: continue
                    for j, q2 in ps:
                        s.usedperm.add(q2)
                        if j != l1: s.covered.add(cls(q2))
                    k2h = ps[l1 + 1][1]
                    m2left[0] -= 1; d4rem[0] -= 1
                    if dfsQ(arc_end(k2h, l2)):
                        m2left[0] += 1; d4rem[0] += 1; return True
                    m2left[0] += 1; d4rem[0] += 1
                    for j, q2 in ps:
                        s.usedperm.discard(q2)
                        if j != l1: s.covered.discard(cls(q2))
        return False
    # q1 arc at 123456
    for l in sorted(rem, reverse=True):
        if rem[l] == 0: continue
        r = place_arc(s, '123456', l)
        if r is None: continue
        rem[l] -= 1
        if dfsQ(arc_end('123456', l)): return True, s.nodes
        rem[l] += 1
        unplace(s, r)
    return False, s.nodes

JOBS = [
 ("job1", 16,0,[3,3],   8, [(1,1)]),
 ("job2", 16,0,[3,2],   8, [(1,2),(2,1)]),
 ("job3", 16,0,[3,1],   8, [(1,3),(3,1),(2,2)]),
 ("job4", 16,0,[2,2],   8, [(1,3),(3,1),(2,2)]),
 ("job5", 15,1,[3,3],   8, [(1,2),(2,1)]),
 ("job6", 15,1,[3,2],   8, [(1,3),(3,1),(2,2)]),
 ("job7", 14,2,[3,3],   8, [(1,3),(3,1),(2,2)]),
 ("job8", 15,0,[3,3,3], 8, [(1,3),(3,1),(2,2)]),
 ("e8j1", 16,0,[3,3,3], 7, [(1,2),(2,1)]),
 ("e7j2", 17,0,[3,3,3], 6, [(1,1)]),
]
if __name__ == '__main__':
    print("independent cross-check of the e=9 stage-2 battery:")
    ok, n = solve(4,0,[],25,[])
    print(f"  ctrl 872 census: {'SAT' if ok else 'UNSAT'} nodes={n}  (expect SAT)")
    assert ok
    allun = True
    for tag, n5, n4, sh, nc, m2 in JOBS:
        ok, n = solve(n5, n4, sh, nc, m2)
        print(f"  {tag}: {'SAT' if ok else 'UNSAT'} nodes={n}")
        if ok: allun = False
    print("CROSS-CHECK VERDICT:", "ALL 8 UNSAT -- agrees with realize.c" if allun
          else "DISAGREEMENT with realize.c -- investigate")
