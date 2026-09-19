
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("my_r1_check: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 6 `assert` statements")
#!/usr/bin/env python3
# R-n6-9: independent clause-by-clause R1/R1' counterexample verification,
# written from proof6.md sect.1 raw definitions only.
import sys, itertools
def rot(p):  return p[1:]+p[0]
def sig(p):  return p[2:]+p[1]+p[0]
def rho(p):  return p[1:5]+p[0]+p[5]
def rotinv(p): return p[5]+p[:5]
def d(p,q):
    for k in range(1,7):
        if p[k:]==q[:6-k]: return k
    return 6

def analyze(S, verbose=False):
    allperms = set(''.join(x) for x in itertools.permutations('123456'))
    # first-occurrence ordering
    order=[]; pos={}; firstpos={}
    for i in range(len(S)-5):
        w=S[i:i+6]
        if w in allperms and w not in pos:
            pos[w]=len(order); order.append(w); firstpos[w]=i
    assert len(order)==720, f"not a superpermutation: {len(order)} perms"
    L=len(S)
    lead=firstpos[order[0]]; trail=L-(firstpos[order[719]]+6)
    dk=[d(order[k],order[k+1]) for k in range(719)]
    gap=[firstpos[order[k+1]]-firstpos[order[k]] for k in range(719)]
    slack=lead+trail+sum(g-dd for g,dd in zip(gap,dk))
    W=sum(dd-1 for dd in dk)
    # runs
    runstart=[0]
    for k in range(719):
        if dk[k]>=2: runstart.append(k+1)
    runends={runstart[i+1]-1 for i in range(len(runstart)-1)} | {719}
    e=len(runstart)-120
    # classes
    cls={}
    for p in allperms:
        c=min(p, *(w for w in [rot(p),rot(rot(p)),rot(rot(rot(p))),rot(rot(rot(rot(p)))),rot(rot(rot(rot(rot(p)))))]))
        cls[p]=c
    # y_C = temporally last element of class C (in the ordering)
    y={}
    for k,p in enumerate(order): y[cls[p]]=k     # overwritten -> last
    crit={C: rot(order[kk]) for C,kk in y.items()}
    critset=set(crit.values())
    assert len(critset)==120
    zq = 0 if order[0] in critset else 1
    # typed transitions
    links={}   # class B -> class C
    cnl=[]; heavies=[]; zh=zp3=zp2s=zp2g=Q2=0; pshits=[]
    for k in sorted(runends):
        if k==719: continue
        z=order[k]; t=order[k+1]; dd=dk[k]
        comp = (y[cls[z]]==k)
        if dd==2:
            if comp:
                assert t==sig(z), "Prop1(e) fail"
                if t in critset:
                    C2=[C for C,cr in crit.items() if cr==t][0]
                    links[cls[z]]=C2
                else: cnl.append(k)
            else:
                if t==rot(rot(z)): Q2+=1; zp2s += (t not in critset)
                elif t==sig(z):
                    if t in critset: pshits.append(k)
                    else: zp2g+=1
                else: assert False, "d=2 dichotomy fail"
        else:
            if comp:
                heavies.append((k,dd,t in critset))
                if t not in critset: zh+=1
            else: zp3+=1
    Z=zq+zh+zp3+zp2s+zp2g
    # link-paths
    entered=set(links.values())
    heads=[C for C in crit if C not in entered]
    paths=[]; pathof={}
    used=set()
    for hcls in heads:
        p=[hcls]; c=hcls
        while c in links: c=links[c]; p.append(c)
        paths.append(p)
        for c in p: pathof[c]=len(paths)-1; used.add(c)
    assert len(used)==120, f"link relation not a path decomposition: {len(used)}"
    # hops: path-end completion d=3 exit landing on another path's head crit
    hops={}
    for i,p in enumerate(paths):
        endc=p[-1]; kk=y[endc]
        if kk==719: continue
        z=order[kk]; t=order[kk+1]
        if kk in runends and d(z,t)==3 and t in critset:
            C2=[C for C,cr in crit.items() if cr==t][0]
            j=pathof[C2]
            if paths[j][0]==C2 and j!=i:    # lands on a HEAD crit of another path
                hops[i]=j
    hopin=set(hops.values())
    chains=[]
    for i in range(len(paths)):
        if i in hopin: continue
        ch=[i]
        while ch[-1] in hops: ch.append(hops[ch[-1]])
        chains.append(ch)
    # m=2 path components: CNL from P1-end -> nc u; z'=rotinv(u) premature ps-exit -> rho(u)=crit(P2 head)
    m2=[]
    runstartset={order[k] for k in runstart}
    for k in cnl:
        zz=order[k]; u=order[k+1]
        P1=pathof[cls[zz]]
        assert paths[P1][-1]==cls[zz], "CNL emitter should end its path"
        zp=rotinv(u)
        kz=pos[zp]
        # z' must be a run end with a premature-sig exit landing on rho(u)
        ok_edge = kz in runends and kz<719 and order[kz+1]==rho(u) and d(zp,order[kz+1])==2
        landing_is_crit = rho(u) in critset
        if ok_edge and landing_is_crit:
            C2=[C for C,cr in crit.items() if cr==rho(u)][0]
            P2=pathof[C2]
            is_head = paths[P2][0]==C2
            # m=2 (not 3): P2's end exit is not another CNL
            endc2=paths[P2][-1]; k2=y[endc2]
            is_m2_end = not (k2 in runends and k2<719 and d(order[k2],order[k2+1])==2 and order[k2+1] not in critset and y[cls[order[k2]]]==k2)
            if is_head:
                m2.append((P1,P2,k,u,is_m2_end))
    return dict(L=L,e=e,Z=Z,zq=zq,zh=zh,zp3=zp3,zp2s=zp2s,zp2g=zp2g,Q2=Q2,slack=slack,W=W,
                paths=paths,chains=chains,hops=hops,m2=m2,order=order,pos=pos,y=y,crit=crit,
                cnl=cnl,pshits=pshits,heavies=heavies,pathof=pathof)

if __name__=='__main__':
    import glob
    total_m2=0; total_viol=0
    for f in sorted(glob.glob('../../../data/counterexamples/m2obj_*.txt')):
        S=open(f).read().strip()
        a=analyze(S)
        viol=0
        details=[]
        for (P1,P2,k,u,ism2) in a['m2']:
            # find the chain headed by P2
            ch=None
            for c in a['chains']:
                if c[0]==P2: ch=c
            selfclose = ch is not None and P1 in ch
            viol += selfclose
            details.append((P1,P2,ism2,selfclose,ch))
        total_m2+=len(a['m2']); total_viol+=viol
        print(f"{f.split('/')[-1]}: L={a['L']} slack={a['slack']} Z={a['Z']} Q2={a['Q2']} e={a['e']} "
              f"m2comps={len(a['m2'])} R1-violations={viol}")
        for dd in details:
            print(f"    P1={dd[0]} P2={dd[1]} m2={dd[2]} launcher-chain-contains-closer={dd[3]}")
    print(f"\nTOTAL m=2 components: {total_m2}, R1 violations: {total_viol}")
