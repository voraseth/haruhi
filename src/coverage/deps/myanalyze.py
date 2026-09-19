
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("myanalyze: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 1 `assert` statements")
#!/usr/bin/env python3
# R-n6-7 reviewer's OWN first-occurrence analyzer, written from proof6.md sect.1
# raw definitions only.  No code shared with the artifact or prior reviews.
import sys
from itertools import permutations

def rot(p): return p[1:] + p[:1]
def rotinv(p): return p[-1] + p[:-1]
def rho(p): return p[1:5] + p[0] + p[5]
def sig(p): return p[2:6] + p[1] + p[0]
def dist(p, q):
    for k in range(0, 7):
        if k == 6 or p[k:] == q[:6-k]:
            return k if k < 6 else 6
    return 6

def analyze(S):
    """Full accounting of a superpermutation string per proof6.md sect.1."""
    N = 720
    first = {}   # perm -> position of first occurrence
    order = []
    for i in range(len(S) - 5):
        w = S[i:i+6]
        if len(set(w)) == 6 and w not in first:
            first[w] = i; order.append(w)
    if len(order) != N: return None
    pos = {q: k for k, q in enumerate(order)}   # ordering index
    d = [dist(order[k], order[k+1]) for k in range(N-1)]
    W = sum(x - 1 for x in d)
    gaps = [first[order[k+1]] - first[order[k]] for k in range(N-1)]
    lead = first[order[0]]
    trail = len(S) - (first[order[-1]] + 6)
    slack = lead + trail + sum(g - dd for g, dd in zip(gaps, d))
    # runs
    run_id = [0]*N
    r = 0
    for k in range(1, N):
        if d[k-1] >= 2: r += 1
        run_id[k] = r
    nruns = r + 1
    e = nruns - 120
    run_start = {}; run_end = {}
    for k in range(N):
        rid = run_id[k]
        if rid not in run_start: run_start[rid] = k
        run_end[rid] = k
    # classes
    def cls(p):
        b = p; q = p
        for _ in range(5):
            q = rot(q)
            if q < b: b = q
        return b
    y = {}          # class -> completion (temporally last member), as ordering index
    for k, q in enumerate(order):
        y[cls(q)] = k
    crit = {c: rot(order[k]) for c, k in y.items()}    # crit(C) = rot(y_C)
    crit_of = {}                                       # perm -> class it is crit of
    for c, w in crit.items(): crit_of[w] = c
    # run start/end perms
    starts = [order[run_start[i]] for i in range(nruns)]
    ends = [order[run_end[i]] for i in range(nruns)]
    completion_end = [ends[i] == order[y[cls(ends[i])]] for i in range(nruns)]
    # transitions and typing
    zq = 0 if order[0] in crit_of else 1
    zh = zp3 = zp2s = zp2g = Q2 = cnl = pshits = 0
    links = []      # (classB, classC)
    hops = []       # (path-end class, head class) filled later
    heavies = []
    h = X4h = X4 = 0
    trans_land = {}  # landing perm -> (k, dk, srcperm)
    for k in range(N-1):
        if d[k] == 1: continue
        z = order[k]; t = order[k+1]
        trans_land[t] = (k, d[k], z)
        is_comp = (k == y[cls(z)])
        if d[k] == 2:
            if is_comp:
                if t in crit_of: links.append((cls(z), crit_of[t]))
                else: cnl += 1
            else:
                if t == rot(rot(z)):
                    Q2 += 1
                    if t not in crit_of: zp2s += 1
                elif t == sig(z):
                    if t in crit_of: pshits += 1
                    else: zp2g += 1
                else:
                    raise AssertionError("d=2 landing neither rot2 nor sig")
        else:
            h += 1
            if d[k] >= 4: X4h += 1; X4 += d[k] - 3
            heavies.append((k, d[k], is_comp))
            if not is_comp: zp3 += 1
            if t not in crit_of: zh += 1
    Z = zq + zh + zp3 + zp2s + zp2g
    # link paths
    nxt = dict(links); prv = {c: b for b, c in links}
    heads = [c for c in y if c not in prv]
    paths = []
    path_of = {}
    for hd in heads:
        pth = [hd]; c = hd
        while c in nxt:
            c = nxt[c]; pth.append(c)
        for c2 in pth: path_of[c2] = len(paths)
        paths.append(pth)
    Pn = len(paths)
    D = sum(5 - len(p) for p in paths)
    # hops: path-end completion d=3 exit landing on a path head crit (of another path)
    hop_pairs = []
    for pi, pth in enumerate(paths):
        endc = pth[-1]
        k = y[endc]
        if k == N-1: continue
        if d[k] == 3:
            t = order[k+1]
            if t in crit_of:
                c2 = crit_of[t]
                pj = path_of[c2]
                if paths[pj][0] == c2 and pj != pi:
                    hop_pairs.append((pi, pj))
    cnxt = dict(hop_pairs); cprv = {b: a for a, b in hop_pairs}
    chain_heads = [i for i in range(Pn) if i not in cprv]
    chains = []
    for ch in chain_heads:
        c = [ch]
        while c[-1] in cnxt: c.append(cnxt[c[-1]])
        chains.append(c)
    NCh = len(chains)
    # pointer graph on runs
    start_run = {starts[i]: i for i in range(nruns)}
    pedges = []   # (tail run, head run, kind, k)
    for k in range(N-1):
        if d[k] != 2: continue
        z = order[k]; t = order[k+1]
        if not (k == y[cls(z)]) and t == rot(rot(z)): continue   # S-exit: no edge
        tail = start_run.get(rot(z)); head = start_run.get(t)
        assert tail is not None and head is not None
        pedges.append((tail, head, k))
    pout = {a: (b, k) for a, b, k in pedges}
    pin = {b: (a, k) for a, b, k in pedges}
    # components
    comp_of = {}
    comps = []
    for i in range(nruns):
        if i in comp_of: continue
        # walk back to source or detect cycle
        seen = {i}
        cur = i
        while cur in pin and pin[cur][0] not in seen:
            cur = pin[cur][0]; seen.add(cur)
        if cur in pin:  # cycle
            cyc = [cur]; nx = pout[cur][0]
            while nx != cur: cyc.append(nx); nx = pout[nx][0]
            for v in cyc: comp_of[v] = len(comps)
            comps.append(('cycle', cyc))
        else:
            path = [cur]
            while path[-1] in pout: path.append(pout[path[-1]][0])
            for v in path: comp_of[v] = len(comps)
            comps.append(('path', path))
    # census: per component, count crit-runs (m paths) and nc runs
    is_crit_run = [starts[i] in crit_of for i in range(nruns)]
    census = {'a1':0,'a2':0,'a3':0,'c1':0,'c2':0}
    comp_paths = []   # per comp: list of link-path indices in order
    for kind, vs in comps:
        ncrit = sum(1 for v in vs if is_crit_run[v])
        ncnc = len(vs) - ncrit
        # m = number of link-paths = number of maximal crit-chains
        pset = []
        for v in vs:
            if is_crit_run[v]:
                pi = path_of[crit_of[starts[v]]]
                if not pset or pset[-1] != pi: pset.append(pi)
        if kind == 'cycle' and pset and len(pset) > 1 and pset[0] == pset[-1]: pset.pop()
        m = len(dict.fromkeys(pset))
        comp_paths.append((kind, pset, vs))
        if kind == 'path':
            if m == 1: census['a1'] += 1
            elif m == 2: census['a2'] += 1
            elif m == 3: census['a3'] += 1
        else:
            if m == 1: census['c1'] += 1
            elif m == 2: census['c2'] += 1
    Ncyc = sum(1 for kind, _ in comps if kind == 'cycle')
    return dict(L=len(S), W=W, slack=slack, e=e, D=D, X4=X4, X4h=X4h,
                Z=Z, zq=zq, zh=zh, zp3=zp3, zp2s=zp2s, zp2g=zp2g, Q2=Q2,
                cnl=cnl, pshits=pshits, Pn=Pn, NCh=NCh, Ncyc=Ncyc,
                census=census, paths=paths, chains=chains, comps=comps,
                comp_paths=comp_paths, order=order, pos=pos, y=y, crit=crit,
                crit_of=crit_of, path_of=path_of, d=d, run_id=run_id,
                starts=starts, ends=ends, run_start=run_start, run_end=run_end,
                pedges=pedges, hop_pairs=hop_pairs, trans_land=trans_land)

if __name__ == '__main__':
    import hashlib
    for f in sys.argv[1:]:
        S = open(f).read().strip()
        a = analyze(S)
        print(f, 'sha256', hashlib.sha256(S.encode()).hexdigest()[:8])
        if a is None:
            print('  NOT A SUPERPERMUTATION'); continue
        print('  L=%d W=%d slack=%d e=%d D=%d X4=%d X4h=%d Z=%d P#=%d NCh=%d Ncyc=%d' %
              (a['L'], a['W'], a['slack'], a['e'], a['D'], a['X4'], a['X4h'],
               a['Z'], a['Pn'], a['NCh'], a['Ncyc']))
        print('  census', a['census'], 'Q2=%d cnl=%d pshits=%d' % (a['Q2'], a['cnl'], a['pshits']))
