#!/usr/bin/env python3
"""Constructive plant of a LOOP-carrying placement (see plant3 docstring).
Stage 1 enumerates self-closing loops around the anchor 123456; stage 2
completes with q1's hop-chain and 25 type-I cycles."""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("plant4: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 1 `assert` statements")
import sys, time
from itertools import permutations
PERMS=[''.join(p) for p in permutations('123456')]; I={p:i for i,p in enumerate(PERMS)}
rot=[I[p[1:]+p[0]] for p in PERMS]; rho=[I[p[1:5]+p[0]+p[5]] for p in PERMS]
rotinv=[0]*720
for i,v in enumerate(rot): rotinv[v]=i
cls=[-1]*720; _n=0
for i in range(720):
    if cls[i]<0:
        q=i
        for _ in range(6): cls[q]=_n; q=rot[q]
        _n+=1
orb=[-1]*720; orbmem=[]
for i in range(720):
    if orb[i]<0:
        m=[];q=i
        for _ in range(5): orb[q]=len(orbmem); m.append(q); q=rho[q]
        orbmem.append(m)
S3=[[I[PERMS[i][3]+PERMS[i][4]+PERMS[i][5]+''.join(t)] for t in permutations(PERMS[i][:3])] for i in range(720)]
byclass=[[] for _ in range(120)]
for p in range(720): byclass[cls[p]].append(p)
occ=[0]*720; cov=[0]*120; placed=[]
def place(x,ln,gap,kind):
    cells=[];p=x
    for k in range(ln):
        if occ[p] or (k!=gap and cov[cls[p]]):
            for m,q in enumerate(cells):
                occ[q]=0
                if m!=gap: cov[cls[q]]=0
            return None
        occ[p]=1
        if k!=gap: cov[cls[p]]=1
        cells.append(p);p=rho[p]
    placed.append((kind,cells,gap)); return cells
def unplace(cells,gap):
    placed.pop()
    for m,q in enumerate(cells):
        occ[q]=0
        if m!=gap: cov[cls[q]]=0
NB=[0]
def cyclefill(k):
    NB[0]+=1
    if NB[0]>4000: return False
    if k==0: return all(cov)
    c=next((c for c in range(120) if not cov[c]),None)
    if c is None: return False
    for p in byclass[c]:
        o=orb[p]
        if any(occ[q] for q in orbmem[o]): continue
        for s in range(5):
            if orbmem[o][s]==p: continue
            cc=place(orbmem[o][0],5,s,'cyc')
            if cc is None: continue
            if cyclefill(k-1): return True
            unplace(cc,s)
    return False
C1=25
def qchain(end,left,arcs,depth=0):
    if left==0:
        NB[0]=0
        return cyclefill(C1)
    if depth>=6: return False
    for x in S3[end]:
        for ln in (5,4,3,2,1):
            if ln>left: continue
            c=place(x,ln,-1,'arc')
            if c is None: continue
            arcs.append(ln)
            if qchain(rotinv[c[ln-1]],left-ln,arcs,depth+1): return True
            arcs.pop(); unplace(c,-1)
    return False
def qstart(left,arcs,limit=40):
    tried=0
    for y in range(720):
        if occ[y]: continue
        tried+=1
        if tried>limit: return False
        for ln in (5,4,3,2,1):
            if ln>left: continue
            c=place(y,ln,-1,'arc')
            if c is None: continue
            arcs.append(ln)
            if qchain(rotinv[c[ln-1]],left-ln,arcs): return True
            arcs.pop(); unplace(c,-1)
    return False
t0=time.time()
for l1 in (1,2,3):
  for l2 in (1,2,3):
    if l1+l2>4: continue
    sp=place(0,l1+1+l2,l1,'span')
    if sp is None: continue
    e0=rotinv[sp[l1+l2]]
    def walk(end,arcs,depth):
        if depth>0 and 0 in S3[end]:
            left=120-4*C1-(l1+l2)-sum(arcs)
            if left>=0:
                arcsB=[]
                if qstart(left,arcsB):
                    return (list(arcs),arcsB)
        if depth>=3: return None
        for x in S3[end]:
            for ln in (5,4,3,2,1):
                c=place(x,ln,-1,'arc')
                if c is None: continue
                arcs.append(ln)
                r=walk(rotinv[c[ln-1]],arcs,depth+1)
                if r is not None: return r
                arcs.pop(); unplace(c,-1)
        return None
    r=walk(e0,[],0)
    if r is not None:
        arcsA,arcsB=r; arcs=arcsA+arcsB
        assert all(cov)
        n={k:arcs.count(k) for k in range(1,6)}
        print("PLANT OK (%.1fs) span=(%d,%d) loop-chain arcs=%s q1-chain arcs=%s cycles=%d"%(time.time()-t0,l1,l2,arcsA,arcsB,C1))
        print("ENGINE ARGS: --n5 %d --n4 %d --n3 %d --n2 %d --n1 %d --c1 %d --spans %d --bq1 0 --x4h 0 --defect none"%(n[5],n[4],n[3],n[2],n[1],C1,l1+l2))
        with open('data/plant.txt','w') as f:
            for kind,cells,gap in placed:
                f.write("%-5s cells=%s gap=%d classes=%s\n"%(kind,cells,gap,[cls[q] for m,q in enumerate(cells) if m!=gap]))
        sys.exit(0)
    unplace(sp,l1)
print("no plant found (%.1fs)"%(time.time()-t0)); sys.exit(1)
