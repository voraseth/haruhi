#!/usr/bin/env python3
"""Clean-room census generator: Algorithm G (alg:census) + Algorithm E (alg:expand)
of PAPER-n6-872-v2.tex, plus the defect-class expansion of Lemma zclass.

Written from the paper's printed specification alone.  Emits:
  - part A: configurations per Z=0 structural class
  - part B: the search instances, each tagged m0 or m0+m1
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("census: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 1 `assert` statements")
import sys, itertools
from math import ceil


NEG = -10**9

# ---------------------------------------------------------------- Table B.1
# The coarse frontier g(c,a,b), Table tab:coarse (rows c=0..20,
# columns g(c,0,0) g(c,1,0) g(c,0,1) g(c,1,1); '--' = no such chain).
_G_ROWS = """
0  4  -  -  -
1  -  4  4  1
2  7  4  4  4
3  7  7  7  4
4  10 7  7  7
5  10 10 10 7
6  11 10 10 10
7  13 11 11 10
8  14 13 13 11
9  15 14 14 13
10 16 15 15 14
11 17 16 16 15
12 19 17 17 16
13 19 19 19 17
14 22 19 19 19
15 22 22 22 19
16 22 22 22 22
17 24 23 23 22
18 24 24 24 23
19 25 25 25 24
20 25 25 25 25
"""
# index by (a,b): column order in the table is (0,0),(1,0),(0,1),(1,1)
_COLS = [(0, 0), (1, 0), (0, 1), (1, 1)]
G = {}
for line in _G_ROWS.strip().splitlines():
    f = line.split()
    c = int(f[0])
    for j, ab in enumerate(_COLS):
        G[(c,) + ab] = NEG if f[1 + j] == '-' else int(f[1 + j])


def cap(c, a, b):
    """Definition def:F: cap(c,a,b)."""
    if c <= 16:
        return G[(c, a, b)]
    if c <= 20:
        return min(25, 4 - 2 * a - 2 * b + 2 * c)
    return 4 - 2 * a - 2 * b + 2 * c


_Fcache = {}


def F(k, m, sh, st):
    """Definition def:F, chain packing function, by dynamic programming."""
    if k < 0 or m < 0:
        return NEG
    key = (k, m, sh, st)
    if key in _Fcache:
        return _Fcache[key]
    sh = min(sh, k)
    st = min(st, k)
    if sh > k or st > k:
        return NEG
    # dp[(cost_used, a_got, b_got)] = best block total, a_got/b_got saturating at sh/st
    dp = {(0, 0, 0): 0}
    for _ in range(k):
        nd = {}
        for (cu, ag, bg), val in dp.items():
            for c in range(0, m - cu + 1):
                for a in (0, 1):
                    for b in (0, 1):
                        v = cap(c, a, b)
                        if v <= NEG // 2:
                            continue
                        st2 = (cu + c, min(sh, ag + a), min(st, bg + b))
                        if nd.get(st2, NEG) < val + v:
                            nd[st2] = val + v
        dp = nd
        if not dp:
            break
    best = NEG
    for (cu, ag, bg), val in dp.items():
        if ag >= sh and bg >= st and val > best:
            best = val
    _Fcache[key] = best
    return best


# ---------------------------------------------------------------- Algorithm G
def census(D, X4, e, X4h):
    """Algorithm alg:census for one Z=0 structural class (D,X4,Z=0,e,X4h)."""
    out = []
    assert D % 5 == 0                                   # G1
    P = 24 + D // 5                                     # G1
    for a2 in range(0, e + 1):
        for a3 in range(0, (e - a2) // 2 + 1):
            for c2 in range(0, (e - a2 - 2 * a3) // 2 + 1):
                c1 = e - a2 - 2 * a3 - 2 * c2
                if c1 < 0:                              # G2
                    continue
                a1 = P - e - a2 - a3
                if a1 < 0:                              # G3
                    continue
                Sc1, Sc2 = 4 * c1, 3 * c2               # G4
                # G5: three-block components contribute length 3*a3
                bqs = (0, 1) if (a2 + a3) >= 1 else (0,)   # G6
                for bq1 in bqs:
                    lam = a2 + a3 + 1 + X4h - bq1          # G7
                    sh_rest = a2 + a3
                    st_rest = max(0, a2 + a3 - bq1)
                    blocks_rest = a1 + 2 * a2 + 2 * a3 - bq1
                    for n5 in range(0, a1 + 1):
                        for n4 in range(0, a1 - n5 + 1):
                            nS = a1 - n5 - n4
                            n45 = n5 + n4
                            Rmax = nS + lam
                            if (n45 > 4 * Rmax or n4 > 2 * Rmax or
                                    max(-(-n45 // 4), -(-n4 // 2)) > Rmax):
                                continue                # G8
                            rem = 120 - 5 * n5 - 4 * n4 - 3 * a3 - Sc1 - Sc2
                            if not (nS + 2 * a2 <= rem <= 3 * nS + 4 * a2):
                                continue                # G9
                            V = P - 2 * D
                            v_sing = ((2 * Sc1 - 9 * c1) + (2 * Sc2 - 18 * c2)
                                      - 7 * a3 - 3 * bq1)
                            if V > v_sing + 4 * lam - 2 * sh_rest - 2 * st_rest:
                                continue                # G10
                            cost_sing = ((5 * c1 - Sc1) + (10 * c2 - Sc2)
                                         + 4 * a3 + 2 * bq1)
                            cost_rest = D - cost_sing
                            if cost_rest < 0:
                                continue                # G11
                            if blocks_rest > F(lam, cost_rest, sh_rest, st_rest):
                                continue                # G11
                            out.append(dict(a2=a2, a3=a3, c1=c1, c2=c2, bq1=bq1,
                                            n45=n45, n4=n4, n5=n5, nS=nS,
                                            Sc1=Sc1, Sc2=Sc2, a1=a1, rem=rem,
                                            lam=lam, X4h=X4h, D=D, e=e, P=P))
    return out


# ---------------------------------------------------------------- Algorithm E
def multisets_le(nparts, lo, hi, total):
    """All non-increasing tuples of length nparts with values in [lo,hi] summing to total."""
    res = []

    def rec(i, maxv, left, acc):
        if i == nparts:
            if left == 0:
                res.append(tuple(acc))
            return
        rest = nparts - i - 1
        for v in range(min(maxv, left - lo * rest), lo - 1, -1):
            if v > hi:
                continue
            if left - v > hi * rest:
                break
            rec(i + 1, v, left - v, acc + [v])
    if nparts == 0:
        if total == 0:
            res.append(())
        return res
    rec(0, hi, total, [])
    return res


def expand(cfg):
    """Algorithm alg:expand."""
    inst = []
    a2, nS, rem = cfg['a2'], cfg['nS'], cfg['rem']
    for spans in multisets_le(a2, 2, 4, None) if False else _span_multisets(a2):
        sigma = rem - sum(spans)                        # E1
        if sigma < 0:                                   # E2
            continue
        for short in multisets_le(nS, 1, 3, sigma):     # E3
            n3 = sum(1 for v in short if v == 3)
            n2 = sum(1 for v in short if v == 2)
            n1 = sum(1 for v in short if v == 1)
            inst.append(dict(n5=cfg['n5'], n4=cfg['n4'], n3=n3, n2=n2, n1=n1,
                             c1=cfg['c1'], spans=tuple(spans), bq1=cfg['bq1'],
                             X4h=cfg['X4h'], defect=None))
    return inst


def _span_multisets(a2):
    return [tuple(sorted(t, reverse=True))
            for t in set(tuple(sorted(c, reverse=True))
                         for c in itertools.product((2, 3, 4), repeat=a2))]


# ------------------------------------------------- defect class (Lemma zclass)
def defect_instances():
    """(15,0,1), e=2.  Two wirings; expansion over s_A in {2,3,4},
    l_B in {1,2,3,4}, and every multiset of one-block deficiencies
    summing to Delta1 = s_A + l_B."""
    inst = []
    for wiring in ('zh', 'zp3'):
        for sA in (2, 3, 4):
            for lB in (1, 2, 3, 4):
                D1 = sA + lB
                for part in _partitions(D1, 4):
                    # one-block components: deficiency d -> path length 5-d
                    n = {1: 0, 2: 0, 3: 0, 4: 0, 5: 0}
                    for d in part:
                        n[5 - d] += 1
                    a1 = 27 - 3          # P=27 link-paths; span 2 + defect 1
                    n[5] += a1 - len(part)
                    inst.append(dict(n5=n[5], n4=n[4], n3=n[3], n2=n[2], n1=n[1],
                                     c1=0, spans=(sA,), bq1=0, X4h=0,
                                     defect=(wiring, lB)))
    return inst


def _partitions(n, maxpart):
    if n == 0:
        return [()]
    res = []
    for v in range(min(n, maxpart), 0, -1):
        for tail in _partitions(n - v, v):
            res.append((v,) + tail)
    return res


# ---------------------------------------------------------------- driver
CLASSES = ([('20-e%d' % e, 20, 0, e, 0) for e in range(1, 10)] +
           [('15-e%d' % e, 15, 1, e, 1) for e in (1, 2, 3, 4, 7)] +
           [('10-e2', 10, 2, 2, 2)])

def main():
    tot_cfg = tot_inst = tot_loop = 0
    per = {}
    lines_cfg, lines_inst = [], []
    for name, D, X4, e, X4h in CLASSES:
        cfgs = census(D, X4, e, X4h)
        ni = nl = 0
        for cfg in cfgs:
            lines_cfg.append("%s %d %d %d %d %d | %d %d %d %d | %d %d | %d %d" % (
                name, cfg['a2'], cfg['a3'], cfg['c1'], cfg['c2'], cfg['bq1'],
                cfg['a1'], cfg['n45'], cfg['n4'], cfg['nS'], cfg['Sc1'],
                cfg['Sc2'], cfg['lam'], cfg['a2'] + 2 * cfg['a3']))
            for I in expand(cfg):
                U = cfg['a2'] + 2 * cfg['a3']
                loop = 1 if U >= 1 else 0
                ni += 1
                nl += loop
                lines_inst.append(fmt_inst(name, I, loop))
        per[name] = (len(cfgs), ni, nl)
        tot_cfg += len(cfgs); tot_inst += ni; tot_loop += nl
    # defect class
    dn = 0
    for I in defect_instances():
        dn += 1
        lines_inst.append(fmt_inst('z1-' + I['defect'][0], I, 1))
    per['z1'] = (0, dn, dn)
    tot_inst += dn; tot_loop += dn

    with open('data/configs.txt', 'w') as f:
        f.write("\n".join(lines_cfg) + "\n")
    with open('data/instances.txt', 'w') as f:
        f.write("\n".join(lines_inst) + "\n")

    def agg(pref):
        c = i = l = 0
        for k, v in per.items():
            if k.startswith(pref):
                c += v[0]; i += v[1]; l += v[2]
        return c, i, l
    print("class group        configs instances loopruns")
    for pref, label in (('20-', '(20,0,0) e=1..9'), ('15-', '(15,1,0) e=1,2,3,4,7'),
                        ('10-', '(10,2,0) e=2'), ('z1', '(15,0,1) defect')):
        c, i, l = agg(pref)
        print("%-22s %5d %8d %8d" % (label, c, i, l))
    print("%-22s %5d %8d %8d" % ('TOTAL', tot_cfg, tot_inst, tot_loop))
    print("runs = %d linear + %d loop = %d" % (tot_inst, tot_loop, tot_inst + tot_loop))


def fmt_inst(name, I, loop):
    d = 'none' if I['defect'] is None else '%s:%d' % I['defect']
    return ("%s n5=%d n4=%d n3=%d n2=%d n1=%d c1=%d spans=%s bq1=%d x4h=%d "
            "defect=%s mode=%s" % (name, I['n5'], I['n4'], I['n3'], I['n2'],
                                   I['n1'], I['c1'],
                                   ",".join(map(str, I['spans'])) or '-',
                                   I['bq1'], I['X4h'], d,
                                   'm0+m1' if loop else 'm0'))


if __name__ == '__main__':
    main()
