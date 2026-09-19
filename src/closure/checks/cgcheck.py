#!/usr/bin/env python3
"""n6cg: build the CLOSURE GRAPH CG under the CORRECTED definition
   V(CG) = hop-chains NOT lying in pointer CYCLE components ("free chains")
and verify Lemma 6.8's structural claims on real objects.
Uses only the raw structural decomposition returned by the independent
R-n6-7 reviewer analyzer (myanalyze.analyze); CG itself is built here."""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("cgcheck: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 1 `assert` statements")
import sys, os, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'src', 'closure', 'deps'))
from myanalyze import analyze, rot


def build_cg(a):
    N = 720
    order=a['order']; d=a['d']; y=a['y']; crit_of=a['crit_of']; path_of=a['path_of']
    paths=a['paths']; chains=a['chains']; comps=a['comps']; comp_paths=a['comp_paths']
    starts=a['starts']; pedges=a['pedges']
    pout={u:(v,k) for u,v,k in pedges}; pin={v:(u,k) for u,v,k in pedges}
    # link-path -> component kind
    pkind={}
    for kind,pset,vs in comp_paths:
        for pi in pset: pkind[pi]=kind
    # chain index of each link-path; chain head/ender path
    chain_of={}
    for ci,ch in enumerate(chains):
        for pi in ch: chain_of[pi]=ci
    # free chains = chains with no link-path in a cycle component
    free=[ci for ci,ch in enumerate(chains) if not any(pkind.get(pi)=='cycle' for pi in ch)]
    freeset=set(free)
    # sanity: a chain is either all-cycle or all-path
    for ci,ch in enumerate(chains):
        ks={pkind.get(pi) for pi in ch}
        assert len(ks)==1, ('mixed chain',ci,ks)
    # ---- arcs: one per chain-ender completion exit ----
    arcs=[]      # (A, B, kind)  kind in {'nc','d4','other'}
    other=[]
    for ci,ch in enumerate(chains):
        endp=ch[-1]; C=paths[endp][-1]; k=y[C]
        if k==N-1:  continue                      # global end
        t=order[k+1]; dk=d[k]
        tgt=None; kind=None
        if dk==2:
            # completion d=2 : link (impossible for a path end) or CNL into an nc run
            if t in crit_of:
                continue                          # link -> not a path end; skip
            # CNL lands on the nc run start t ; that nc run's out-edge gives the ps-hit
            v=a['run_id'][a['pos'][t]] if t in a['pos'] else None
            v={s:i for i,s in enumerate(starts)}.get(t)
            if v is not None and v in pout:
                w=pout[v][0]; s=starts[w]
                if s in crit_of: tgt=path_of[crit_of[s]]; kind='nc'
        elif dk>=4 and t in crit_of:
            tgt=path_of[crit_of[t]]; kind='d4'
        elif dk>=3 and t not in crit_of:
            kind='other'                          # zh-style defect join
        elif dk==3 and t in crit_of:
            continue                              # a hop: not a chain ender
        if tgt is None:
            other.append((ci,dk,kind)); continue
        cj=chain_of[tgt]
        arcs.append((ci,cj,kind))
    # restrict to free chains
    farcs=[(u,v,kd) for u,v,kd in arcs if u in freeset and v in freeset]
    dropped=[(u,v,kd) for u,v,kd in arcs if not(u in freeset and v in freeset)]
    return dict(chains=chains,free=free,freeset=freeset,arcs=arcs,farcs=farcs,
                dropped=dropped,other=other,chain_of=chain_of,pkind=pkind)

def decompose(V, E):
    """E: list of (u,v). Returns (n_sources,n_sinks,loops,indeg_ok,outdeg_ok)."""
    outd={}; ind={}
    nxt={}
    for u,v in E:
        outd[u]=outd.get(u,0)+1; ind[v]=ind.get(v,0)+1
        nxt.setdefault(u,v)
    ok_out=all(outd.get(x,0)<=1 for x in V)
    ok_in =all(ind.get(x,0)<=1 for x in V)
    srcs=[x for x in V if ind.get(x,0)==0]
    snks=[x for x in V if outd.get(x,0)==0]
    # loops = vertices not reachable from any source
    seen=set()
    for s in srcs:
        c=s
        while c is not None and c not in seen:
            seen.add(c); c=nxt.get(c)
    loops=[]
    rest=set(V)-seen
    while rest:
        s=rest.pop(); cyc=[s]; c=nxt.get(s)
        while c is not None and c!=s:
            cyc.append(c); rest.discard(c); c=nxt.get(c)
        loops.append(cyc)
    return srcs,snks,loops,ok_in,ok_out

def report(fn):
    S=open(fn).read().strip()
    S=''.join(ch for ch in S if ch.isdigit())
    a=analyze(S)
    if a is None: print(fn,'NOT A SUPERPERM'); return
    g=build_cg(a); cen=a['census']
    a2,a3,c1,c2=cen['a2'],cen['a3'],cen['c1'],cen['c2']
    X4h=a['X4h']
    V=g['free']; E=[(u,v) for u,v,_ in g['farcs']]
    srcs,snks,loops,ok_in,ok_out=decompose(V,E)
    kindmap={(u,v):kd for u,v,kd in g['farcs']}
    nd4=sum(1 for u,v,kd in g['farcs'] if kd=='d4')
    nnc=sum(1 for u,v,kd in g['farcs'] if kd=='nc')
    pred=a2+2*a3+1+X4h
    U=a2+2*a3
    loops_ok=all(any(kindmap.get((cy[i],cy[(i+1)%len(cy)]))!='d4'
                     for i in range(len(cy))) for cy in loops)
    print('%-28s L=%d e=%d D=%d X4h=%d Z=%d  a1=%d a2=%d a3=%d c1=%d c2=%d NCh=%d'%(
        os.path.basename(fn),a['L'],a['e'],a['D'],X4h,a['Z'],
        cen['a1'],a2,a3,c1,c2,a['NCh']))
    print('    |V(CG)|=%d  predicted a2+2a3+1+X4h=%d  %s | |E|=%d (nc=%d d4=%d) pred=%d %s'%(
        len(V),pred,'OK' if len(V)==pred else '**MISMATCH**',
        len(E),nnc,nd4,U+X4h,'OK' if len(E)==U+X4h else '**MISMATCH**'))
    print('    indeg<=1:%s outdeg<=1:%s  sources=%d sinks=%d  loops k=%d  U=%d  k<=U:%s  every loop has non-d4 arc:%s'%(
        ok_in,ok_out,len(srcs),len(snks),len(loops),U,len(loops)<=U,loops_ok))
    if g['dropped']: print('    arcs touching cycle chains (dropped):',len(g['dropped']))
    if g['other']:  print('    unresolved enders:',g['other'][:5])
    return dict(L=a['L'],V=len(V),pred=pred,E=len(E),k=len(loops),U=U,
                ok_in=ok_in,ok_out=ok_out,src=len(srcs),snk=len(snks),loops_ok=loops_ok)

if __name__=='__main__':
    res=[report(f) for f in sys.argv[1:]]
    bad=[r for r in res if r and (r['V']!=r['pred'] or not r['ok_in'] or not r['ok_out']
         or r['src']!=1 or r['snk']!=1 or r['k']>r['U'] or not r['loops_ok'])]
    print('\n%d objects, %d violations'%(len(res),len(bad)))
