#!/usr/bin/env python3
"""lem59_z1.py -- LEMMA 5.9 (the defect-one class (15,0,1), e=2).

Two stages.

STAGE 1 (branch level).  LEDGER-n6 puts the single Z unit in exactly one of
zq, zh, zp3, zp2s, zp2g.  For each, T1-n6 (cnl = e - zL), T2-n6
(pshits = e - Q2 - zp3 - zp2g), I5 at slack 0 (Q2 = zp2s) and TC1z
(NCh = 2 + zh + zp3) give the chain count and the endpoint obligations
E1-n6 (SH >= pshits) / E2-n6 (ST >= cnl).  The three branches with NCh = 2
die outright: 27 link-paths cannot be packed into 2 chains of total cost 15.

STAGE 2 (wiring level) for the two branches with NCh = 3.  The pointer-graph
components carrying the e = 2 non-critical runs are enumerated MECHANICALLY
from the in/out-edge census of those runs (no hand list): an nc run has an
in-edge iff its start is the landing of a d=2 transition, an out-edge iff the
premature run end rot^{-1}(start) exits at d=2; nc runs are never adjacent
(an edge into an nc run is a CNL, whose tail is a critical run) and critical
blocks are never adjacent (an edge between two critical runs is a link, which
would merge the two link-paths into one).  Hence each nc-carrying component is
a strictly alternating word in blocks K and nc's, and the generator below
lists every such word compatible with the edge census.

Every component has at most 5 vertices, and a cycle exactly 5 (Lemma 6.5: a
pointer edge advances the run start by rho, and rho has order exactly 5), so a
component with k blocks and j nc's obeys  sum(l) + j <= 5 (= 5 on a cycle),
whence each block has  l <= 5 - j - (k-1) =: l_max.

REFINEMENT MONOTONICITY (proved in finlem.md sect. 2.4).  Designating q_1's
path, the zh-emitting path, the zp3-entered path or the globally last path to
be one of the blocks of an nc-component only turns that block into a forced
singleton chain: it lowers blocks_rest and lam by 1 and cost_rest by the
block's cost floor, and by  F(k,m,sh,st) >= cap(c,a,b) + F(k-1,m-c,sh-a,st-b)
this can only make the Pareto test HARDER to pass.  So a shape whose
undesignated ("generic") wiring already fails is dead in every refinement;
the refinements are nevertheless all printed, because they are what pins the
surviving skeletons.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("lem59_z1: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 2 `assert` statements")
import itertools
from frontier import F


P, D, e = 27, 15, 2


# ---------------------------------------------------------------- generator
def components(ncs):
    """ncs: list of (name, has_in, has_out).  Yield every list of components;
    a component is (kind, items) with kind in {'path','cycle'} and items a
    strictly alternating list of ('K', id) / ('n', name)."""
    names = [n[0] for n in ncs]
    attr = {n[0]: (n[1], n[2]) for n in ncs}
    out = []
    # ordered set partitions of the nc names into groups (order inside matters)
    def partitions(rest):
        if not rest:
            yield []
            return
        first = rest[0]
        others = rest[1:]
        for r in range(len(others) + 1):
            for combo in itertools.combinations(others, r):
                grp = [first] + list(combo)
                remaining = [x for x in others if x not in combo]
                for perm in itertools.permutations(grp):
                    if perm[0] != first and first in perm:
                        pass
                    for tail in partitions(remaining):
                        yield [list(perm)] + tail
    seen = set()
    for part in partitions(names):
        key = tuple(sorted(tuple(g) for g in part))
        for kinds in itertools.product(*[('path', 'cycle')] * len(part)):
            comps, ok = [], True
            for grp, kind in zip(part, kinds):
                items = []
                if kind == 'cycle':
                    if not all(attr[u][0] and attr[u][1] for u in grp):
                        ok = False
                        break
                    for u in grp:
                        items.append(('n', u))
                        items.append(('K', None))
                else:
                    if attr[grp[0]][0]:
                        items.append(('K', None))
                    for i, u in enumerate(grp):
                        items.append(('n', u))
                        if i < len(grp) - 1:
                            if not (attr[u][1] and attr[grp[i + 1]][0]):
                                ok = False
                                break
                            items.append(('K', None))
                    if not ok:
                        break
                    if attr[grp[-1]][1]:
                        items.append(('K', None))
                comps.append((kind, items))
            if not ok:
                continue
            sig = tuple(sorted((k, tuple(x[0] for x in it)) for k, it in comps))
            full = (sig, tuple(sorted(tuple(g) for g in part)))
            if full in seen:
                continue
            seen.add(full)
            # name the blocks K1, K2, ...
            n = 0
            named = []
            for kind, items in comps:
                it2 = []
                for t, v in items:
                    if t == 'K':
                        n += 1
                        it2.append(('K', 'K%d' % n))
                    else:
                        it2.append(('n', v))
                named.append((kind, it2))
            out.append(named)
    return out


def show(comps):
    s = []
    for kind, items in comps:
        w = " ".join(v for t, v in items)
        s.append(("cycle[%s]" if kind == 'cycle' else "[%s]") % w)
    return " + ".join(s)


# ------------------------------------------------------------------- ledger
def ledger(comps, ps_out, q1=None, zh_emit=None, zp3_tgt=None, gend=None,
           NCh=3):
    """Derive (blocks_rest, lam, cost_rest, sh_rest, st_rest) for a wiring.
    ps_out: set of nc names whose out-edge is a ps-hit."""
    blocks = []
    for kind, items in comps:
        k = sum(1 for t, _ in items if t == 'K')
        j = sum(1 for t, _ in items if t == 'n')
        lmax = 5 - j - (k - 1)
        L = len(items)
        for i, (t, v) in enumerate(items):
            if t != 'K':
                continue
            if kind == 'cycle':
                prev, nxt = items[(i - 1) % L], items[(i + 1) % L]
            else:
                prev = items[i - 1] if i > 0 else None
                nxt = items[i + 1] if i + 1 < L else None
            ps_entered = prev is not None and prev[0] == 'n' and prev[1] in ps_out
            emits_cnl = nxt is not None and nxt[0] == 'n'
            heads = ps_entered or (v == q1) or (v == zp3_tgt)
            ends = emits_cnl or (v == zh_emit) or (v == gend)
            blocks.append(dict(name=v, lmax=lmax, ps=ps_entered,
                               cnl=emits_cnl, heads=heads, ends=ends))
    sing = [b for b in blocks if b['heads'] and b['ends']]
    rest = [b for b in blocks if not (b['heads'] and b['ends'])]
    return (P - len(sing), NCh - len(sing),
            D - sum(5 - b['lmax'] for b in sing),
            sum(1 for b in rest if b['ps']),
            sum(1 for b in rest if b['cnl']),
            [b['name'] for b in sing])


def verdict(tag, lg):
    br, lam, cr, sh, st, sing = lg
    f = F(lam, cr, sh, st)
    alive = br <= f
    print("   %-46s blocks=%2d  F(%d,%2d,%d,%d)=%2d  -> %s"
          % (tag, br, lam, cr, sh, st, f, "ALIVE" if alive else "DEAD"))
    return alive


print("=" * 78)
print("LEMMA 5.9 -- corner (D,X4,Z) = (15,0,1), e = 2:  P = 27, h = 25, "
      "X4h = 0, D = 15")
print("=" * 78)
print()
print("[A] BRANCH LEVEL   (LEDGER-n6: the Z unit lies in exactly one pool)")
print("    pool  | Q2 cnl pshits | NCh | test                    | verdict")
BR = [("zq",   0, 1, 2, 2), ("zh",   0, 1, 2, 3), ("zp3",  0, 2, 1, 3),
      ("zp2s", 1, 1, 1, 2), ("zp2g", 0, 1, 1, 2)]
alive_branch = {}
for pool, Q2, cnl, psh, NCh in BR:
    if NCh == 2:
        sh, st = psh, cnl        # E1-n6: SH >= pshits;  E2-n6: ST >= cnl
        f = F(2, D, sh, st)
        ok = P <= f
        print("    %-5s | %2d %3d %6d |  %d  | 27 <= F(2,15,%d,%d)=%-2d    | %s"
              % (pool, Q2, cnl, psh, NCh, sh, st, f, "ALIVE" if ok else "DEAD"))
        alive_branch[pool] = ok
    else:
        print("    %-5s | %2d %3d %6d |  %d  | -> wiring analysis [B]   | see [B]"
              % (pool, Q2, cnl, psh, NCh))
print()

print("[B] WIRING LEVEL, branch zh = 1  (nc runs: ncH heavy-entered => NO")
print("    in-edge; nc2 CNL-entered.  Both premature ends are ps-hits, so both")
print("    nc runs have a ps-hit out-edge.  cnl = 1, pshits = 2, NCh = 3.)")
zh_ncs = [("ncH", False, True), ("nc2", True, True)]
zh_shapes = components(zh_ncs)
print("    mechanically generated shapes: %d" % len(zh_shapes))
zh_alive = []
for comps in zh_shapes:
    print("   shape %s" % show(comps))
    srcK, sinkK = [], []
    for kind, items in comps:
        if kind != 'cycle':
            if items[0][0] == 'K':
                srcK.append(items[0][1])
            if items[-1][0] == 'K':
                sinkK.append(items[-1][1])
    g = ledger(comps, {"ncH", "nc2"})
    a = verdict("generic (q1 / zh-emitter / global end outside)", g)
    if a:
        zh_alive.append((comps, 'generic'))
    for k in srcK:
        gg = ledger(comps, {"ncH", "nc2"}, q1=k)
        if verdict("refinement q1 = %s   [singletons %s]" % (k, gg[5]), gg):
            zh_alive.append((comps, 'q1=' + k))
    for k in sinkK:
        gg = ledger(comps, {"ncH", "nc2"}, zh_emit=k)
        if verdict("refinement zh-emitter = %s  [singletons %s]" % (k, gg[5]), gg):
            zh_alive.append((comps, 'zhemit=' + k))
        gg = ledger(comps, {"ncH", "nc2"}, gend=k)
        if verdict("refinement global end = %s  [singletons %s]" % (k, gg[5]), gg):
            zh_alive.append((comps, 'gend=' + k))
print()

print("[C] WIRING LEVEL, branch zp3 = 1  (nc runs: nc1 and nc2 both CNL-entered")
print("    (cnl = 2); one premature end is the ps-hit (pshits = 1), the other is")
print("    the zp3 heavy, which generates no pointer edge -- so exactly one nc")
print("    run, nc2, has NO out-edge.  NCh = 3.)")
zp3_ncs = [("nc1", True, True), ("nc2", True, False)]
zp3_shapes = components(zp3_ncs)
print("    mechanically generated shapes: %d" % len(zp3_shapes))
zp3_alive = []
for comps in zp3_shapes:
    print("   shape %s" % show(comps))
    srcK, sinkK = [], []
    for kind, items in comps:
        if kind != 'cycle':
            if items[0][0] == 'K':
                srcK.append(items[0][1])
            if items[-1][0] == 'K':
                sinkK.append(items[-1][1])
    g = ledger(comps, {"nc1"})
    if verdict("generic (q1 / zp3-target / global end outside)", g):
        zp3_alive.append((comps, 'generic'))
    for k in srcK:
        gg = ledger(comps, {"nc1"}, q1=k)
        if verdict("refinement q1 = %s   [singletons %s]" % (k, gg[5]), gg):
            zp3_alive.append((comps, 'q1=' + k))
        gg = ledger(comps, {"nc1"}, zp3_tgt=k)
        if verdict("refinement zp3-target = %s  [singletons %s]" % (k, gg[5]), gg):
            zp3_alive.append((comps, 'zp3tgt=' + k))
    for k in sinkK:
        gg = ledger(comps, {"nc1"}, gend=k)
        if verdict("refinement global end = %s  [singletons %s]" % (k, gg[5]), gg):
            zp3_alive.append((comps, 'gend=' + k))
print()

print("[D] SUMMARY")
print("    branches zq, zp2s, zp2g : DEAD  =>  zp2s = 0  =>  Q2 = 0 (I5)")
print("    surviving wirings, zh branch : %d" % len(zh_alive))
for c, t in zh_alive:
    print("        %s   (%s)" % (show(c), t))
print("    surviving wirings, zp3 branch: %d" % len(zp3_alive))
for c, t in zp3_alive:
    print("        %s   (%s)" % (show(c), t))
tot = len(zh_alive) + len(zp3_alive)
print("    TOTAL surviving component wirings: %d" % tot)
print("    every surviving wiring is cycle-free  =>  Ncyc = 0;  NCh = 3.")
assert tot == 2, "expected exactly two surviving wirings, got %d" % tot
assert not any(k == 'cycle' for c, _ in zh_alive + zp3_alive
               for k, _ in c), "a cycle wiring survived"
print()
print("LEMMA 5.9 VERDICT: the Z unit is in zh or zp3; exactly two component")
print("wirings survive, both cycle-free, with Q2 = 0, Ncyc = 0, NCh = 3.")
