"""validate871.py -- INDEPENDENT n=6 ordering analyser and lemma validator.

Written from the raw definitions of proof6.md section 1; shares no code with
approaches/n6/checks/lib6.py.  Every lemma the L=871 argument uses is asserted
on every object, with SPECIAL emphasis on the NEW guards:
   GROUPS-n6   (pointer components carry whole crit-chains; k_g >= m_g - 1,
                and >= m_g for cycles; <= 5 vertices)
   PARETOS-n6  (at least Ns = PEN hop-chains are a single short link-path)
   CHAINRUN-n6 (per-chain run structure: r <= s4+1-a3-b3, <=4 blocks/run,
                <= 2 length-4 blocks per run)
Every lemma below holds for EVERY ordering of the 720 permutations (proof6.md
section 2: "All parts hold for every first-occurrence ordering on [6]; no length
hypothesis"), so the corpus can be arbitrary orderings -- the widest possible.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("validate871: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 13 `assert` statements")
import itertools, random, sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

P = list(itertools.permutations((1,2,3,4,5,6)))
IX = {p:i for i,p in enumerate(P)}
def rot(p): return p[1:]+p[:1]
def sig(p): return p[2:]+(p[1],p[0])
def rho(p): return p[1:5]+p[:1]+p[5:]
def dd(p,q):
    for k in range(1,7):
        if p[k:]==q[:6-k]: return k
    return 6
ROT=[IX[rot(p)] for p in P]; SIG=[IX[sig(p)] for p in P]; RHO=[IX[rho(p)] for p in P]
def cid(i):
    m=i;c=i
    for _ in range(5):
        c=ROT[c]; m=min(m,c)
    return m
CLS=[cid(i) for i in range(720)]
CLASSES=sorted(set(CLS)); CIX={c:i for i,c in enumerate(CLASSES)}
assert len(CLASSES)==120
DTAB=[[0]*720 for _ in range(720)]
for i in range(720):
    pi=P[i]; row=DTAB[i]
    for j in range(720): row[j]=dd(pi,P[j])

class Obj:
    def __init__(self, order):
        assert len(order)==720 and len(set(order))==720
        self.q=order
        pos={p:i for i,p in enumerate(order)}
        self.pos=pos
        # runs
        runs=[[0]]
        for i in range(1,720):
            if ROT[order[i-1]]==order[i]: runs[-1].append(i)
            else: runs.append([i])
        self.runs=runs; self.nruns=len(runs); self.e=len(runs)-120
        self.runof=[0]*720
        for ri,r in enumerate(runs):
            for i in r: self.runof[order[i]]=ri
        self.startperm=[order[r[0]] for r in runs]
        self.endperm=[order[r[-1]] for r in runs]
        self.runat={self.startperm[ri]:ri for ri in range(self.nruns)}
        assert len(self.runat)==self.nruns
        # y_C and crits
        last={}
        for i,p in enumerate(order): last[CLS[p]]=p
        self.y=last
        self.crit={c:ROT[last[c]] for c in CLASSES}
        self.critset=set(self.crit.values())
        assert len(self.critset)==120
        # every crit is a run start (Prop 2a)
        for c in CLASSES: assert self.crit[c] in self.runat, "crit not a run start"
        # transitions
        self.d=[DTAB[order[i]][order[i+1]] for i in range(719)]
        # classify run ends
        self.zq = 0 if order[0] in self.critset else 1
        Q2=zp3=zp2s=zp2g=zh=0
        cnl=0; links={}; self.edges=[]
        self.heavy=0; self.X4h=0; self.X4=0
        self.exit_of_end={}
        for ri,r in enumerate(runs):
            i=r[-1]
            if i==719: self.exit_of_end[ri]=None; continue
            z=order[i]; t=order[i+1]; w=self.d[i]
            comp = (z==last[CLS[z]])
            self.exit_of_end[ri]=(z,t,w,comp)
            if w>=3:
                self.heavy+=1
                if w>=4: self.X4h+=1; self.X4+=w-3
                if t not in self.critset: zh+=1
                if not comp: zp3+=1
            elif w==2:
                if comp:
                    assert t==SIG[z], "completion d=2 must land on sig(y)"
                    if t in self.critset:
                        links[CLS[z]]=CLS[t]
                    else:
                        cnl+=1
                    self.edges.append((self.runat[ROT[z]], self.runat[t]))
                else:
                    if t==ROT[ROT[z]]:
                        Q2+=1
                        if t not in self.critset: zp2s+=1
                    else:
                        assert t==SIG[z], "premature d=2 must be rot^2 or sig"
                        if t not in self.critset: zp2g+=1
                        self.edges.append((self.runat[ROT[z]], self.runat[t]))
        self.Q2,self.zp3,self.zp2s,self.zp2g,self.zh,self.cnl=Q2,zp3,zp2s,zp2g,zh,cnl
        self.Z=self.zq+zh+zp3+zp2s+zp2g
        self.links=links
        # link-paths
        indeg=set(links.values())
        self.paths=[]
        for c in CLASSES:
            if c in indeg: continue
            path=[c]
            while path[-1] in links: path.append(links[path[-1]])
            self.paths.append(path)
        assert sum(len(p) for p in self.paths)==120, "link relation not a path system"
        self.Pnum=len(self.paths)
        self.D=5*self.Pnum-120
        self.Fp=sum(1 for p in self.paths if len(p)==5)
        self.S5=sum(1 for p in self.paths if len(p)==4)
        self.S4=sum(1 for p in self.paths if len(p)<=3)
        self.Sp=self.S5+self.S4
        self.headof={p[0]:i for i,p in enumerate(self.paths)}
        # hops -> chains
        self.hop={}
        for i,p in enumerate(self.paths):
            zend=last[p[-1]]
            j=self.pos[zend]
            if j==719: continue
            if self.d[j]!=3: continue
            t=self.q[j+1]
            for k,pp in enumerate(self.paths):
                if k!=i and self.crit[pp[0]]==t: self.hop[i]=k
        hin=set(self.hop.values())
        self.chains=[]
        for i in range(self.Pnum):
            if i in hin: continue
            ch=[i]
            while ch[-1] in self.hop: ch.append(self.hop[ch[-1]])
            self.chains.append(ch)
        assert sum(len(c) for c in self.chains)==self.Pnum, "hop relation not a path system"
        self.NCh=len(self.chains)
        # pointer components
        out={}; inn={}
        for a,b in self.edges:
            assert a not in out and b not in inn, "pointer degree > 1"
            out[a]=b; inn[b]=a
        self.comps=[]; seen=set()
        for v in range(self.nruns):
            if v in seen: continue
            comp=set(); st=[v]
            while st:
                u=st.pop()
                if u in comp: continue
                comp.add(u)
                if u in out: st.append(out[u])
                if u in inn: st.append(inn[u])
            seen|=comp
            iscyc = all(u in out and u in inn for u in comp)
            self.comps.append((comp,iscyc))
        self.Ncomp=len(self.comps); self.Ncyc=sum(1 for _,c in self.comps if c)
        # chain endpoint types / Ns
        self.SH=sum(1 for c in self.chains if len(self.paths[c[0]])<5)
        self.ST=sum(1 for c in self.chains if len(self.paths[c[-1]])<5)
        self.Ns=sum(1 for c in self.chains if len(c)==1 and len(self.paths[c[0]])<5)
        self.pshits=sum(1 for ri,ex in self.exit_of_end.items() if ex and ex[2]==2
                        and not ex[3] and ex[1]==SIG[ex[0]] and ex[1] in self.critset)

FAILS=[]
TOTALRETR=[0]
RETRACTION=[]   # components with zp2g = 0 and k_g > m_g: the retraction witness
def check(o, tag):
    def A(cond,msg):
        if not cond: FAILS.append((tag,msg))
    # -- registered accounting
    A(o.Pnum==24+o.D//5, "PNUM")
    A(o.heavy==23+o.D//5+o.Z-o.e, "UNIT")
    A(o.cnl==o.e-(o.zq+o.zh+o.zp2s+o.zp2g), "T1")
    A(o.pshits==o.e-o.Q2-o.zp3-o.zp2g, "T2")
    A(o.Ncyc+o.Q2<=o.e, "L12")
    A(o.SH>=o.pshits and o.pshits<=o.Sp, "E1")
    A(o.ST>=o.cnl and o.cnl<=o.Sp, "E2")
    A(o.Ns>=max(0,o.pshits+o.cnl-o.Sp), "E3")
    A(o.Ns>=o.Ncyc-o.zp2g, "LEMMAC")
    A(o.NCh<=1+o.X4h+o.zh+o.cnl, "T7")
    if o.Z==0: A(o.D>=o.e+5*(o.e-o.Q2-o.Ncyc), "LU8")
    # -- NEW: the component / GROUPS lemma
    A(o.Ncomp==o.Pnum-o.cnl+o.Q2+o.zp3+o.Ncyc, "NCOMP formula")
    pathof={}
    for i,pp in enumerate(o.paths):
        for c in pp: pathof[c]=i
    for comp,iscyc in o.comps:
        A(len(comp)<=5, "L2 component size")
        crit_runs=[u for u in comp if o.startperm[u] in o.critset]
        nc=len(comp)-len(crit_runs)
        pids=set(pathof[CLS[o.startperm[u]]] for u in crit_runs)
        m=len(pids)
        # whole crit-chains lie inside
        tot=sum(len(o.paths[i]) for i in pids)
        A(tot==len(crit_runs), "crit-chain not contained in component")
        A(tot+nc==len(comp), "component vertex split")
        if o.Z==0: A(m>=1, "component with no crit-run at Z=0")
        A(nc>=m-(0 if iscyc else 1), "k_g >= m_g - [not cycle]")
        # the component must match a DECLARED group type
        import scan871 as S
        lens=sorted(len(o.paths[i]) for i in pids)
        d5=sum(1 for x in lens if x==5); d4=sum(1 for x in lens if x==4)
        ds4=sum(1 for x in lens if x<=3); dd=sum(5-x for x in lens if x<=3)
        hit=False
        for (mm,cok,nok,k,e5,e4,es4,edd,gp,gc) in S._group_types():
            if (mm,k,e5,e4,es4,edd)==(m,nc,d5,d4,ds4,dd) and ((cok if iscyc else nok)):
                hit=True; break
        A(hit, f"component type not in GROUPTYPES: m={m} k={nc} lens={lens} cyc={iscyc}")
    # -- NEW: GROUPS feasibility must ACCEPT the real object (ALL Z).
    # Only for D <= 60: the feasibility DP is a search whose cost explodes for
    # the wildly sub-optimal random objects, and the habitat lives at D <= 25.
    if o.D <= 60:
        import scan871 as S
        A(S.groups_feasible(o.Ncomp,o.Ncyc,o.Pnum,o.e,o.Fp,o.S5,o.S4,o.D,o.zp2g,o.zq+o.zh+o.zp2s),
          f"GROUPS rejected a REAL object  Ncomp={o.Ncomp} Ncyc={o.Ncyc} P#={o.Pnum} "
          f"e={o.e} Fp={o.Fp} S5={o.S5} S4={o.S4} D={o.D}")
    # -- NEW: per-chain run structure (CHAINRUN)
    for ch in o.chains:
        L=[len(o.paths[i]) for i in ch]
        s5=sum(1 for x in L if x==4); s4=sum(1 for x in L if x<=3)
        cost=sum(5-x for x in L if x<5)
        a=1 if L[0]<5 else 0; b=1 if L[-1]<5 else 0
        a3=1 if L[0]<=3 else 0; b3=1 if L[-1]<=3 else 0
        r=0; inrun=False
        for x in L:
            if x>=4:
                if not inrun: r+=1; inrun=True
            else: inrun=False
        A(r<=s4+1-a3-b3 or r==0, "CHAINRUN r <= s4+1-a3-b3")
        A(len(L)<=s4+4*r, "CHAINRUN blocks <= s4+4r")
        A(s5<=2*r or r==0, "CHAINRUN s5 <= 2r")
        # certified run caps inside every maximal {4,5}-run
        cur=[]
        for x in L+[0]:
            if x>=4: cur.append(x)
            else:
                if cur:
                    A(len(cur)<=4, "RUNCAP 4")
                    A(sum(1 for y in cur if y==4)<=2, "RUNFOURCAP 2")
                    A(all(y==5 for y in cur[1:-1]), "no interior four")
                cur=[]
        mb=S_maxblocks(cost,s5,s4,a,b)
        A(mb is not None and len(L)<=mb, f"CHAINRUN maxblocks {L}")
    # -- RETRACTION WITNESS (control-check Rn6-4).  The ALTERNATION accounting is
    # asserted here component by component, in its CORRECT form, and the corpus
    # is required to EXHIBIT the configuration that refutes the sentence this
    # artifact previously printed ("at zp2g = 0 this forces k_g <= m_g").
    out={}; inn={}
    for a,b in o.edges: out[a]=b; inn[b]=a
    zp2gedge=set()
    for ri,ex in o.exit_of_end.items():
        if ex is None: continue
        z,t,w,cmp_ = ex
        if w==2 and not cmp_ and t==SIG[z] and t not in o.critset:
            zp2gedge.add((o.runat[ROT[z]], o.runat[t]))
    for comp,iscyc in o.comps:
        cr=[u for u in comp if o.startperm[u] in o.critset]
        m=len(set(pathof[CLS[o.startperm[u]]] for u in cr)); k=len(comp)-len(cr)
        if iscyc: start=next(iter(comp))
        else: start=[u for u in comp if u not in inn][0]
        seqv=[]; u=start
        while True:
            seqv.append(u)
            if u not in out: break
            u=out[u]
            if u==start or len(seqv)>=len(comp): break
        A(len(seqv)==len(comp), "component walk did not cover the component")
        isnc=[o.startperm[v] not in o.critset for v in seqv]
        nb=0; prev=False
        for x in isnc:
            if x and not prev: nb+=1
            prev=x
        if iscyc and isnc and isnc[0] and isnc[-1] and nb>1: nb-=1   # cyclic wrap
        pairs=[(seqv[i],seqv[i+1]) for i in range(len(seqv)-1)]
        if iscyc: pairs.append((seqv[-1],seqv[0]))
        g2in=sum(1 for pr in pairs if pr in zp2gedge)
        # The identity and the cycle clause hold for m_g >= 1.  A component with
        # NO crit-run is degenerate: its nc-runs form ONE block, which for a
        # cycle wraps and so carries k_g zp2g edges rather than k_g - 1.
        if m >= 1:
            A(k == nb + g2in,
              f"ALT: k_g = nb + internal zp2g failed (k={k} nb={nb} g2={g2in})")
            if iscyc: A(nb == m, f"ALT: cycle must have nb = m_g (nb={nb} m={m})")
            else:     A(m-1 <= nb <= m+1, f"ALT: path needs nb in m-1..m+1 (nb={nb} m={m})")
            if (not iscyc) and nb == m+1:
                A(isnc and isnc[0], "ALT: nb = m_g+1 without an nc-run SOURCE")
        else:
            A(nb == 1, f"ALT: an nc-only component must be ONE block (nb={nb})")
            A(k == g2in + (0 if iscyc else 1),
              f"ALT: nc-only component edge count (k={k} g2={g2in} cyc={iscyc})")
        if o.zp2g == 0:
            A(k <= m+1, f"ALT: zp2g=0 must give k_g <= m_g + 1 (k={k} m={m})")
            if k > m:
                RETRACTION.append((tag, m, k, nb, bool(isnc and isnc[0]),
                                   bool(isnc and isnc[-1]), iscyc))
                TOTALRETR[0] += 1

    # -- NEW: the m = 0 (nc-only) component BUDGETS used by GROUPS
    g2used=0; srcused=0
    for comp,iscyc in o.comps:
        cr=[u for u in comp if o.startperm[u] in o.critset]
        if cr: continue
        g2used += len(comp) if iscyc else len(comp)-1
        if not iscyc: srcused += 1
    A(g2used<=o.zp2g, f"m=0 groups use more zp2g edges than exist ({g2used}>{o.zp2g})")
    A(srcused<=o.zq+o.zh+o.zp2s,
      f"m=0 path groups exceed zq+zh+zp2s ({srcused}>{o.zq+o.zh+o.zp2s})")
    # -- NEW: PARETOS -- at least PEN chains are a single short path
    OV=max(0,o.SH+o.ST-o.Sp); PEN=max(OV,o.Ncyc-o.zp2g)
    A(o.Ns>=PEN, "PARETOS Ns >= PEN")

def S_maxblocks(c,s5,s4,a,b):
    import scan871 as S
    return S._maxblocks(c,s5,s4,a,b)

# ------------------------------------------------------------------ corpus
def greedy(seed, eps):
    rnd=random.Random(seed)
    cur=0; seen={0}; order=[0]
    while len(order)<720:
        best=None
        for w in range(1,7):
            cand=[q for q in range(720) if q not in seen and DTAB[cur][q]==w]
            if cand:
                if eps and rnd.randrange(100)<eps:
                    alt=[]
                    for w2 in range(w+1,7):
                        alt=[q for q in range(720) if q not in seen and DTAB[cur][q]==w2]
                        if alt: break
                    if alt: cand=alt
                best=rnd.choice(cand); break
        cur=best; seen.add(best); order.append(best)
    return order

def classblock(seed, full_prob):
    rnd=random.Random(seed)
    byc={}
    for i in range(720): byc.setdefault(CLS[i],[]).append(i)
    keys=list(byc); rnd.shuffle(keys)
    order=[]; seen=set()
    for k in keys:
        x=rnd.choice(byc[k])
        m=6 if rnd.random()<full_prob else rnd.randint(1,5)
        for _ in range(m):
            if x not in seen: order.append(x); seen.add(x)
            x=ROT[x]
    rest=[i for i in range(720) if i not in seen]
    rnd.shuffle(rest)
    # append the leftovers as class arcs so that e stays moderate
    for i in rest:
        if i not in seen: order.append(i); seen.add(i)
    return order

def perturb(seq, seed, nmoves):
    rnd=random.Random(seed)
    s=list(seq)
    for _ in range(nmoves):
        i=rnd.randrange(0,700); L=rnd.choice((1,2,3,6,6,12))
        chunk=s[i:i+L]; del s[i:i+L]
        j=rnd.randrange(0,len(s))
        s[j:j]=chunk
    return s

# --------------------------------------------------------------------------
# TARGET-REGIME generator: real Z = 0 orderings with SMALL D and e >= 1, i.e.
# exactly the regime the L=871 corners live in.  Built from a partition of the
# 120 classes into 24 pairwise class-disjoint rho-orbits.  A "type A" unit
# sweeps the orbit's 5 classes as 5 full runs of 6 (one FULL link-path); a
# "type B" unit realises the pointer-CYCLE pattern
#     [crit-arc of C4 : rot^1..rot^5 of rho^4(x)]  (ends prematurely at z)
#     [C0][C1][C2][C3] as full runs of 6           (a length-4 link-path)
#     [nc-arc of C4 : rho^4(x) alone]              (the CNL landing, y_{C4})
# whose z-exit is a premature-sig d=2 landing on the crit x -- a ps-hit closing
# a 5-vertex pointer cycle.  Units are joined by d >= 3 jumps onto crits, so
# zq = zh = zp3 = zp2s = zp2g = 0 and Z = 0 exactly.
def rho_orbit_cover(seed):
    """24 pairwise class-disjoint rho-orbits covering all 120 classes
    (exact cover, Algorithm X with the min-remaining-options class first)."""
    rnd=random.Random(seed)
    orbits=[]; seenp=set()
    for i in range(720):
        if i in seenp: continue
        orb=[i]; c=i
        for _ in range(4): c=RHO[c]; orb.append(c)
        for c in orb: seenp.add(c)
        orbits.append(orb)
    assert len(orbits)==144
    sets=[]
    for orb in orbits:
        cs=frozenset(CLS[p] for p in orb)
        assert len(cs)==5
        sets.append((cs,orb))
    opts={c:[] for c in CLASSES}
    for si,(cs,_) in enumerate(sets):
        for c in cs: opts[c].append(si)
    used=set(); chosen=[]
    def dfs():
        if len(chosen)==24: return True
        rem=[c for c in CLASSES if c not in used]
        if not rem: return len(chosen)==24
        best=min(rem, key=lambda c: sum(1 for si in opts[c] if not (sets[si][0]&used)))
        cand=[si for si in opts[best] if not (sets[si][0]&used)]
        rnd.shuffle(cand)
        for si in cand:
            used.update(sets[si][0]); chosen.append(si)
            if dfs(): return True
            chosen.pop(); used.difference_update(sets[si][0])
        return False
    if not dfs(): return None
    return [sets[si][1] for si in chosen]

def unitA(x):
    out=[]
    c=x
    for _ in range(5):
        y=c
        for _ in range(6): out.append(y); y=ROT[y]
        c=RHO[c]
    return out, x, out[-1]

def unitB(x):
    c4=x
    for _ in range(4): c4=RHO[c4]          # c4 = rho^4(x)
    out=[]
    y=ROT[c4]
    for _ in range(5): out.append(y); y=ROT[y]   # crit-arc of C4, ends at rot^5(c4)
    c=x
    for _ in range(4):
        y=c
        for _ in range(6): out.append(y); y=ROT[y]
        c=RHO[c]
    out.append(c4)                                # nc-arc of C4 = {y_{C4}}
    return out, ROT[c4], c4

def target_object(seed, nB):
    cov=rho_orbit_cover(seed)
    if cov is None: return None
    rnd=random.Random(seed*7919+nB)
    heads=[]
    for orb in cov:
        heads.append(orb[rnd.randrange(5)])
    kinds=[1]*nB+[0]*(24-nB); rnd.shuffle(kinds)
    units=[]
    for h,k in zip(heads,kinds):
        units.append(unitB(h) if k else unitA(h))
    # order the units so that every join is a d >= 3 jump onto the next entry
    order=list(range(24)); 
    for _ in range(400):
        bad=[i for i in range(23) if DTAB[units[order[i]][2]][units[order[i+1]][1]]<3]
        if not bad: break
        i=rnd.choice(bad); j=rnd.randrange(24)
        order[i],order[j]=order[j],order[i]
    if any(DTAB[units[order[i]][2]][units[order[i+1]][1]]<3 for i in range(23)):
        return None
    seq=[]
    for i in order: seq.extend(units[i][0])
    if len(set(seq))!=720: return None
    return seq

WITNESS = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__))))), 'reviews', 'tests', 'Rn6-4',
    'alt_counterexample.txt')

def from_string(path):
    txt=open(path).read().split()[0].strip()
    seen=set(); order=[]
    for i in range(len(txt)-5):
        w=tuple(int(c) for c in txt[i:i+6])
        if len(set(w))==6 and w not in seen: seen.add(w); order.append(IX[w])
    assert len(order)==720, path
    return order

if __name__=="__main__":
    import scan871 as S
    here=os.path.dirname(os.path.abspath(__file__))
    N=int(sys.argv[1]) if len(sys.argv)>1 else 200
    objs=0; hist={}; prof=[]; nom1=0
    for s in range(N):
        for mk in (lambda: greedy(s,0), lambda: greedy(s,15), lambda: greedy(s,40),
                   lambda: classblock(s,0.9), lambda: classblock(s,0.5),
                   lambda: classblock(s,0.15), lambda: classblock(s,0.99),
                   lambda: classblock(s,0.75), lambda: classblock(s,0.3)):
            try: o=Obj(mk())
            except AssertionError as ex:
                FAILS.append(("build",str(ex))); continue
            check(o,f"seed{s}")
            objs+=1
            pathof={}
            for i,pp in enumerate(o.paths):
                for c in pp: pathof[c]=i
            for comp,iscyc in o.comps:
                cr=[u for u in comp if o.startperm[u] in o.critset]
                if not cr: nom1+=1
            prof.append((o.Z,o.e,o.D,o.Ncyc,o.Ncomp,o.S5,o.S4,o.Fp,o.NCh,o.Ns))
            hist[(o.Z==0, min(o.e,40)//5, min(o.D,60)//10)]=hist.get((o.Z==0,min(o.e,40)//5,min(o.D,60)//10),0)+1
    print(f"objects analysed = {objs}")
    z0=sum(v for k,v in hist.items() if k[0])
    print(f"  of which Z=0 (where GROUPS applies) = {z0}")
    print(f"  e/D coverage buckets = {len(hist)}")
    z0=[x for x in prof if x[0]==0]
    print(f"  Z=0 objects: {len(z0)}; e range {min((x[1] for x in z0),default=-1)}..{max((x[1] for x in z0),default=-1)}"
          f"; D range {min((x[2] for x in z0),default=-1)}..{max((x[2] for x in z0),default=-1)}"
          f"; Ncyc max {max((x[3] for x in z0),default=-1)}")
    print(f"  components with NO crit-run (must be 0 at Z=0, may be >0 otherwise): {nom1}")
    print(f"  all objects: e range {min(x[1] for x in prof)}..{max(x[1] for x in prof)},"
          f" D range {min(x[2] for x in prof)}..{max(x[2] for x in prof)},"
          f" Ncyc max {max(x[3] for x in prof)}")
    # ---- target-regime objects (small D, e >= 1) and perturbations of them
    tgt=0; tz=[]
    for seed in range(10):
        for nB in range(0,7):
            sq=target_object(seed,nB)
            if sq is None: continue
            o=Obj(sq); check(o,f"tgt{seed}/{nB}"); tgt+=1; tz.append((o.Z,o.e,o.D))
            for pk in range(4):
                sp=perturb(sq,seed*100+nB*10+pk,1+pk)
                try: op=Obj(sp)
                except AssertionError as ex: FAILS.append(("perturb",str(ex))); continue
                check(op,f"pert{seed}/{nB}/{pk}"); tgt+=1; tz.append((op.Z,op.e,op.D))
    small=[t for t in tz if t[2]<=60]
    print(f"target-regime objects = {tgt}; with D<=60 (GROUPS DP actually run) = {len(small)}")
    if small:
        print(f"   Z range {min(t[0] for t in small)}..{max(t[0] for t in small)}, "
              f"e range {min(t[1] for t in small)}..{max(t[1] for t in small)}, "
              f"D range {min(t[2] for t in small)}..{max(t[2] for t in small)}")
        print(f"   with Z>0 and D<=60: {sum(1 for t in small if t[0]>0)}")
    # ---- census SPLIT: does the refuting configuration occur among structured,
    # ---- near-optimal ("banked-like") objects, or only away from them?
    def _census(objs, label):
        RETRACTION.clear()
        for oo in objs: check(oo, label)
        return len(RETRACTION)
    _st=[]; _pt=[]
    for seed in range(6):
        for nB in range(0,7):
            sq=target_object(seed,nB)
            if not sq: continue
            _st.append(Obj(sq))
            for pk in range(4):
                try: _pt.append(Obj(perturb(sq,seed*100+nB*10+pk,1+pk)))
                except AssertionError: pass
    print(f"RETR-STRUCTURED {_census(_st,'structured')}")
    print(f"RETR-PERTURBED {_census(_pt,'perturbed')}")
    BASE=os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(
        os.path.dirname(os.path.abspath(__file__))))),'shared','baseline6.txt')
    print(f"RETR-BASELINE {_census([Obj(from_string(BASE))],'baseline873')}")
    # ---- the registered control-check witness (a VERIFIED superpermutation of
    # ---- length 894) must be analysable and must EXHIBIT the retraction
    B872 = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(
        os.path.dirname(os.path.abspath(__file__))))), 'shared', 'best872.txt')
    if os.path.exists(B872):
        check(Obj(from_string(B872)), "verified872")
        print("verified 872 included in the corpus")
    if os.path.exists(WITNESS):
        ow=Obj(from_string(WITNESS)); check(ow,"Rn6-4-witness")
        print(f"WITNESS-LEN {len(open(WITNESS).read().split()[0].strip())}")
        print(f"WITNESS-ZH {ow.zh}")
        print(f"control-check witness: zp2g={ow.zp2g} zh={ow.zh} zq={ow.zq} zp2s={ow.zp2s} "
              f"e={ow.e} D={ow.D} Z={ow.Z}")
    print(f"RETRACTION-TOTAL {TOTALRETR[0]}")
    print(f"RETRACTION witnesses (zp2g = 0 and k_g > m_g) = {TOTALRETR[0]}")
    if TOTALRETR[0] and RETRACTION:
        m,k,nb = RETRACTION[0][1], RETRACTION[0][2], RETRACTION[0][3]
        print(f"   e.g. m_g={m} k_g={k} nb={nb} source-is-nc={RETRACTION[0][4]} "
              f"sink-is-nc={RETRACTION[0][5]} cycle={RETRACTION[0][6]}")
        print("RETRACTED CLAIM REFUTED BY THE CORPUS")
    else:
        print("RETRACTED CLAIM NOT REFUTED BY THIS CORPUS -- the corpus is the wrong sample")
    if FAILS:
        print(f"VIOLATIONS = {len(FAILS)}")
        seenm=set()
        for t,m in FAILS:
            if m[:60] not in seenm:
                seenm.add(m[:60]); print("   ",t,m)
    else:
        print("ALL N6-871 LEMMA CHECKS PASSED")

