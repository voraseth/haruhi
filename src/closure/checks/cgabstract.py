#!/usr/bin/env python3
"""n6cg: ABSTRACT control for Lemma 6.8.
No real object in the repo has a_3 > 0 or b_q1 = 1, so the two candidate
vertex-set definitions coincide on all of them.  This script builds the
abstract chain/closure structure of a configuration DIRECTLY from TC1-end +
TC3 (the only facts the lemma uses) for configurations WITH a_3 > 0 and/or
b_q1 = 1, and checks Lemma 6.8's claims under
   (A) CORRECTED  V = chains not lying in pointer cycles          ("free")
   (B) AS-PRINTED V = chains that are not forced singletons       ("nonsing")
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("cgabstract: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 5 `assert` statements")
import random, itertools, sys


def build(a1,a2,a3,c1,c2,X4h,bq1,rng):
    # ---- link-paths ----
    P=[]                      # (comp_kind, comp_id, pos, m)
    def add(k,cid,pos,m): P.append((k,cid,pos,m)); return len(P)-1
    a1p=[add('a1',i,1,1) for i in range(a1)]
    a2p=[[add('a2',i,j+1,2) for j in range(2)] for i in range(a2)]
    a3p=[[add('a3',i,j+1,3) for j in range(3)] for i in range(a3)]
    c1p=[[add('c1',i,1,1)] for i in range(c1)]
    c2p=[[add('c2',i,j+1,2) for j in range(2)] for i in range(c2)]
    cyc=set(x for g in c1p+c2p for x in g)
    # ---- q1's path ----
    if bq1:
        assert a2+a3>=1
        q1 = a2p[0][0] if a2 else a3p[0][0]     # position-1 path of a multi comp
    else:
        assert a1>=1
        q1 = a1p[0]
    # ---- TC3 forced boundaries ----
    forced_head=set(); forced_end=set()
    for g in a2p+a3p:
        for j,p in enumerate(g):
            if j>=1: forced_head.add(p)
            if j<=len(g)-2: forced_end.add(p)
    for g in c1p+c2p:
        for p in g: forced_head.add(p); forced_end.add(p)
    forced_head.add(q1)
    # X4h d4-entered heads / d4-emitting enders: choose among paths free to be so
    cand_h=[p for p in a1p if p not in forced_head and p!=q1]
    cand_t=[p for p in a1p if p not in forced_end]
    rng.shuffle(cand_h); rng.shuffle(cand_t)
    d4_heads=cand_h[:X4h]; assert len(d4_heads)==X4h
    cand_t=[p for p in cand_t if p not in d4_heads]
    d4_ends=cand_t[:X4h]; assert len(d4_ends)==X4h
    heads=sorted(forced_head|set(d4_heads)); ends=sorted(forced_end|set(d4_ends))
    # global end: one more ender
    rest_t=[p for p in a1p if p not in ends and p not in heads]
    if not rest_t:
        rest_t=[p for p in a1p if p not in ends]
    gend=rest_t[0]; ends=sorted(set(ends)|{gend})
    NCh=len(heads); assert NCh==len(ends), (NCh,len(ends))
    # ---- assemble chains: match heads to enders ----
    # TC3.6 forced singletons, EXACTLY: cycle paths, a3 middles, q1's path if bq1
    tc3_sing=set(x for g in c1p+c2p for x in g)|set(g[1] for g in a3p)|({q1} if bq1 else set())
    self_both=[p for p in heads if p in ends]        # must be singleton chains
    fh=[p for p in heads if p not in self_both]; fe=[p for p in ends if p not in self_both]
    rng.shuffle(fe)
    chains=[[p] for p in self_both]+[[h,t] for h,t in zip(fh,fe)]
    # sprinkle leftover a1 paths as interiors
    used=set(x for c in chains for x in c)
    for p in a1p:
        if p in used: continue
        c=rng.choice([c for c in chains if len(c)>=2]); c.insert(len(c)-1,p)
    chain_of={p:i for i,c in enumerate(chains) for p in c}
    # ---- arcs (Lemma 5.1 inventory) ----
    arcs=[]
    for g in a2p+a3p:                 # one arc per nc run of a PATH component
        for j in range(len(g)-1): arcs.append((chain_of[g[j]],chain_of[g[j+1]],'nc'))
    for g in c1p+c2p:                 # cycle-internal arcs (dropped from CG)
        for j in range(len(g)): arcs.append((chain_of[g[j]],chain_of[g[(j+1)%len(g)]],'cy'))
    for h,t in zip(d4_heads,d4_ends): arcs.append((chain_of[t],chain_of[h],'d4'))
    return dict(chains=chains,chain_of=chain_of,arcs=arcs,cyc=cyc,q1=q1,gend=gend,
                NCh=NCh,forced_sing=set(chain_of[p] for p in tc3_sing))

def decomp(V,E):
    nxt={}; ind={}; outd={}
    for u,v in E:
        outd[u]=outd.get(u,0)+1; ind[v]=ind.get(v,0)+1; nxt.setdefault(u,v)
    srcs=[x for x in V if ind.get(x,0)==0]; snks=[x for x in V if outd.get(x,0)==0]
    seen=set()
    for s in srcs:
        c=s
        while c is not None and c not in seen: seen.add(c); c=nxt.get(c)
    loops=[]; rest=set(V)-seen
    while rest:
        s=rest.pop(); cy=[s]; c=nxt.get(s)
        while c is not None and c!=s: cy.append(c); rest.discard(c); c=nxt.get(c)
        loops.append(cy)
    return srcs,snks,loops,all(ind.get(x,0)<=1 for x in V),all(outd.get(x,0)<=1 for x in V)

def check(cfg,rng,verbose=False):
    a1,a2,a3,c1,c2,X4h,bq1=cfg
    B=build(a1,a2,a3,c1,c2,X4h,bq1,rng)
    ch=B['chains']; co=B['chain_of']; U=a2+2*a3
    cycch=set(co[p] for p in B['cyc'])
    outA=[]; outB=[]
    for name,Vset in (('A-corrected',[i for i in range(len(ch)) if i not in cycch]),
                      ('B-asprinted',[i for i in range(len(ch)) if i not in B['forced_sing']])):
        Vs=set(Vset)
        E=[(u,v) for u,v,k in B['arcs'] if k!='cy' and u in Vs and v in Vs]
        dropped=[(u,v,k) for u,v,k in B['arcs'] if k!='cy' and not(u in Vs and v in Vs)]
        kind={(u,v):k for u,v,k in B['arcs']}
        s,t,loops,oi,oo=decomp(Vset,E)
        pred=a2+2*a3+1+X4h
        ok=(len(Vset)==pred and oi and oo and len(s)==1 and len(t)==1 and
            s[0]==co[B['q1']] and t[0]==co[B['gend']] and len(loops)<=U and
            not dropped)
        d4only=any(all(kind.get((cy[i],cy[(i+1)%len(cy)]))=='d4' for i in range(len(cy))) for cy in loops)
        rec=dict(name=name,V=len(Vset),pred=pred,E=len(E),drop=len(dropped),d4only=d4only,
                 src=len(s),snk=len(t),srcq1=(len(s)==1 and s[0]==co[B['q1']]),
                 k=len(loops),U=U,indeg=oi,outdeg=oo,ok=ok)
        (outA if name.startswith('A') else outB).append(rec)
    return outA[0],outB[0]

def crit(r):
    """Lemma 6.8 structural claims.  The 'k <= U' clause is waived exactly when
    the random wiring produced a d4-only loop, which the TEMPORAL Lemma 5.3
    forbids in a real ordering but which this abstract model cannot see."""
    return (r['V']==r['pred'] and r['indeg'] and r['outdeg'] and r['src']==1
            and r['snk']==1 and r['srcq1'] and r['drop']==0
            and (r['d4only'] or r['k']<=r['U']))

if __name__=='__main__':
    rng=random.Random(20260904)
    cfgs=[]
    for a2 in range(0,4):
      for a3 in range(0,3):
        for c1 in (0,2):
          for c2 in (0,1):
            for X4h in (0,1,2):
              for bq1 in (0,1):
                if bq1 and a2+a3==0: continue
                a1=14-a2-a3
                if a1<X4h*2+3: continue
                cfgs.append((a1,a2,a3,c1,c2,X4h,bq1))
    nA=nB=n=0; failB={}; nd4=0
    for cfg in cfgs:
        for _ in range(20):
            rA,rB=check(cfg,rng); n+=1
            nA+=crit(rA); nB+=crit(rB); nd4+=rA['d4only']
            if not crit(rB):
                k=(cfg[2]>0,cfg[6]==1); failB[k]=failB.get(k,0)+1
    print('%d configurations x 20 random wirings = %d trials'%(len(cfgs),n))
    print('A  CORRECTED  V = chains not lying in pointer cycles  : %d/%d pass'%(nA,n))
    print('B  AS PRINTED V = chains that are not forced singletons: %d/%d pass'%(nB,n))
    print('   B failures keyed by (a3>0, b_q1=1):',failB)
    print('   (trials whose random wiring made a d4-only loop, waived by Lemma 5.3: %d)'%nd4)
    r=random.Random(7); a,b=check((11,1,1,2,0,1,1),r)
    print()
    print('witness  a1=11 a2=1 a3=1 c1=2 c2=0 X4h=1 b_q1=1  (U=3, pred |V|=5):')
    print('  A:',{k:a[k] for k in ("V","pred","E","drop","src","snk","srcq1","k")}, 'PASS' if crit(a) else 'FAIL')
    print('  B:',{k:b[k] for k in ("V","pred","E","drop","src","snk","srcq1","k")}, 'PASS' if crit(b) else 'FAIL')
