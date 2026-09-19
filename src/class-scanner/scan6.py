"""scan6.py -- n=6 Theorem-M corner scanner.

SETTING.  For a superpermutation S on [6] of length L,
    L = 6 + 719 + W + slack,   slack >= 0                       [cite: T0]
    W = 142 + D/5 + X4 + Z                                      [cite: THMM]
    h = 23 + D/5 + Z - e >= 0                                   [cite: UNIT]
    P# = 24 + D/5                                               [cite: PNUM]
    W >= 143 for every first-occurrence ordering on [6]          [cite: P1]
so a hypothetical length-L string has W + slack = L - 725, and for each rung
B := W - 142 the slack is exactly (L - 725) - (142 + B).

Every guard below carries a cite tag whose name resolves in CITES to the
VERBATIM statement of the n=6 lemma it implements; selfcheck6.py checks that
each such statement occurs verbatim in proof6.md (content-anchored citation),
that every `G.on(...)` guard switch carries a cite tag on its own line or an
adjacent one, and that a malformed or placeholder tag -- anything that is not a
bare CITES key inside the brackets -- FAILS the lint.  All numeric constants of all guards live in DEFAULTS and are
overridable by the gate's semantic-teeth mutations.

NOT USED BY DEFAULT (see UNPROVEN below and proof6.md section 11a): LU19-n6 and
LU15-n6 were restated from the n=7 stock but are NOT re-proved at n=6, so their
guards are OFF.  They are verdict-neutral over the published range L = 868..873,
which the gate measures rather than asserts.
"""

CITES = {
 "T0":    "T0-n6 (slack identity). For every superpermutation S on [6], "
          "L = 6 + 719 + W + slack with slack = lead + trail + sum_k (gap_k - d_k) >= 0.",
 "THMM":  "THMM-n6 (Theorem M at n=6). For every first-occurrence ordering on [6], "
          "W = 142 + D/5 + X4 + Z.",
 "UNIT":  "UNIT-n6 (unit identity). For every first-occurrence ordering on [6], "
          "h = 23 + D/5 + Z - e, and h >= 0.",
 "PNUM":  "PNUM-n6 (path count). For every first-occurrence ordering on [6], "
          "P# = 24 + D/5; equivalently 5*P# - 120 = D.",
 "P1":    "P1-n6 (imported premise). Every first-occurrence ordering on [6] has W >= 143 "
          "(equivalently t >= 24); this is the registered L(6) >= 868.",
 "LEDGER":"LEDGER-n6. Z = zq + zh + zp3 + zp2s + zp2g exactly, with zq in {0,1}.",
 "T1":    "T1-n6. cnl = e - zL exactly, where zL = zq + zh + zp2s + zp2g.",
 "T2":    "T2-n6. pshits = e - Q2 - zp3 - zp2g exactly.",
 "LEMMAS":"LEMMAS-n6 (slack-parametric Lemma S). For every superpermutation on [6], "
          "Q2 - zp2s <= floor((slack - lead - trail)/4); in particular slack <= 3 forces Q2 = zp2s.",
 "L12":   "L12-n6. For every first-occurrence ordering on [6], Ncyc + Q2 <= e.",
 "LU8":   "LU8-n6 (Z = 0 only). If Z = 0 then D >= e + 5*(e - Q2 - Ncyc).",
 "E1":    "E1-n6. SH >= pshits and pshits <= S_p: every ps-hit heads a distinct "
          "hop-chain whose first link-path is short.",
 "E2":    "E2-n6. ST >= cnl and cnl <= S_p: every CNL ends a distinct hop-chain "
          "whose last link-path is short.",
 "E3":    "E3-n6. Ns >= max(0, pshits + cnl - S_p): a link-path that is both ps-started "
          "and CNL-emitting is a singleton hop-chain.",
 "LEMMAC":"LEMMAC-n6 (cycle lemma). Ns >= Ncyc - zp2g: every pointer cycle that contains "
          "a crit-run yields a distinct singleton short hop-chain.",
 "T7":    "T7-n6. NCh <= 1 + X4h + zh + cnl, and X4h <= X4.",
 "DEFSPLIT":"DEFSPLIT-n6. Writing S5 for the number of link-paths of length 4 and S4 for the "
          "number of link-paths of length <= 3, D = S5 + sum over the S4 paths of (5 - l), each "
          "such term lying in {2,3,4}; and S_p = S5 + S4.",
 "LEMMAA":"LEMMAA-n6 (aggregate). P# - 2D <= 4*NCh - 2*SH - 2*ST - PEN, "
          "where PEN = max(max(0, SH + ST - S_p), Ncyc - zp2g).",
 "LEMMAR":"LEMMAR-n6 (run accounting). With R the number of maximal {4,5}-runs, "
          "F_p + S5 <= 4R, S5 <= 2R, and R <= 1 + X4h + zh + cnl + S4.",
 "PARETO":"PARETO-n6 (chain Pareto). For every hop-chain of cost c, with a = 1 iff its "
          "first link-path is short and b = 1 iff its last one is short: blocks <= the "
          "(a,b) entry of PARETO_TABLE at cost c when c <= 16 (running maximum over "
          "costs <= c), and blocks <= 4 - 2a - 2b + 2c for every c. Hence "
          "P# <= F(NCh, D, SH, ST), the maximum of the sum of those caps over NCh "
          "chains of total cost D of which at least SH have a = 1 and at least ST have b = 1.",
 "PARETOS":"PARETOS-n6 (singleton-forced chain Pareto). At least Ns hop-chains are a "
          "single short link-path, contributing exactly one link-path and at least one unit "
          "of deficiency each. Hence for any lower bound ns on Ns we have D >= ns and "
          "P# <= ns + F(NCh - ns, D - ns, max(0, SH - ns), max(0, ST - ns)), with F as in "
          "PARETO-n6; the scanner uses ns = PEN.",
 "LU19":  "LU19-n6 (RESTATED, NOT RE-PROVED AT n=6, GUARD OFF BY DEFAULT). "
          "D >= (e - Z) + 5*max(0, Q2 - 3Z).",
 "LU15":  "LU15-n6 (RESTATED, NOT RE-PROVED AT n=6, GUARD OFF BY DEFAULT). "
          "F_p <= 4*(1 + X4 + Z + S_p - max(0, e - Q2 - Z)).",
}

# guards whose n=6 statement is NOT re-proved in proof6.md; never on by default
UNPROVEN = ('lu19','lu15')

PARETO_TABLE = [
  (4, -1, -1, -1),   # cost 0
  (-1, 4, 4, 1),   # cost 1
  (7, 4, 4, 4),   # cost 2
  (7, 7, 7, 4),   # cost 3
  (10, 7, 7, 7),   # cost 4
  (10, 10, 10, 7),   # cost 5
  (11, 10, 10, 10),   # cost 6
  (13, 11, 11, 10),   # cost 7
  (14, 13, 13, 11),   # cost 8
  (15, 14, 14, 13),   # cost 9
  (16, 15, 15, 14),   # cost 10
  (17, 16, 16, 15),   # cost 11
  (19, 17, 17, 16),   # cost 12
  (19, 19, 19, 17),   # cost 13
  (22, 19, 19, 19),   # cost 14
  (22, 22, 22, 19),   # cost 15
  (22, 22, 22, 22),   # cost 16
]

# index order inside a PARETO_TABLE row: (a,b) = (0,0), (1,0), (0,1), (1,1)
_ABIX={(0,0):0,(1,0):1,(0,1):2,(1,1):3}
PARETO_CMAX=len(PARETO_TABLE)-1
_ENV={}
for _ab,_i in _ABIX.items():
    _best=-10**6
    for _c in range(PARETO_CMAX+1):
        _v=PARETO_TABLE[_c][_i]
        if _v>=0: _best=max(_best,_v)
        _ENV[(_c,_ab)]=_best

import functools
def _cap(c,a,b,slop,cc,ep):
    """Upper bound on the number of link-paths in a hop-chain of cost c whose
    first/last path is short iff a/b.  For c <= PARETO_CMAX: the certified
    table, taken as a running maximum over costs <= c so the bound is monotone.
    For c > PARETO_CMAX: the certified value cap blocks - 2*cost <= B_ff - 2a - 2b,
    written with the SAME constants Lemma A uses (cc = CHAINCAP = B_ff,
    ep = ENDPEN = the certified per-short-endpoint gap), so that a mutation of
    either is visible here too."""
    if c<=PARETO_CMAX:
        v=_ENV[(c,(a,b))]
        return None if v<0 else v+slop
    return cc-ep*a-ep*b+2*c+slop

@functools.lru_cache(maxsize=None)
def pareto_F(k,m,sa,sb,slop,cc=4,ep=2):
    if k==0: return 0 if (m==0 and sa==0 and sb==0) else -10**6
    if sa>k or sb>k: return -10**6
    best=-10**6
    for a in (0,1):
        for b in (0,1):
            for c in range(m+1):
                v=_cap(c,a,b,slop,cc,ep)
                if v is None: continue
                r=pareto_F(k-1,m-c,max(0,sa-a),max(0,sb-b),slop,cc,ep)
                if r>-10**5 and v+r>best: best=v+r
    return best

DEFAULTS = dict(
    PARETO_SLOP=0,   # teeth hook: +k blocks allowed in every per-chain cap
    PARETOS_NS=1,    # teeth hook: multiplier on the forced singleton-short count
    NCLASS=120,      # (n-1)! rotation classes
    FL=5,            # full link-path length n-1
    NM2=4,           # n-2 : deficiency cap of a single short link-path
    SLACKDIV=4,      # n-2 : slack cost of an S-exit that is not a zp2s unit
    THMM_CONST=142,  # Theorem M additive constant
    PNUM_BASE=24,    # P# = PNUM_BASE + D/FL
    UNIT_BASE=23,    # h = UNIT_BASE + D/FL + Z - e
    CHAINCAP=4,      # certified free per-chain value cap
    ENDPEN=2,        # certified penalty per short chain endpoint
    SINGPEN=1,       # certified extra penalty for a single-short chain
    T7_BASE=1,       # NCh <= T7_BASE + X4h + zh + cnl
    LU8_COEF=5,      # D >= e + LU8_COEF*(e - Q2 - Ncyc)   (Z=0)
    LU19_COEF=5,     # D >= (e - Z) + LU19_COEF*max(0, Q2 - 3Z)   (guard off)
    RUNCAP=4,        # certified {4,5}-run block cap
    RUNFOURCAP=2,    # certified {4,5}-run cap on length-4 blocks
    LU15_COEF=4,     # (guard off)
    COND=None,       # conditional-mutation hook: fn(name, ctx) -> override or None
)

# every switchable guard, for the gate's ablation sweep
ALL_GUARDS=('lemmaA','lemmaAweak','lemmaS','lu8','lu19','lu15','lemmaR','pareto','paretos',
            'l12','t7','e1sp','e2sp','e3','lemmaC','defsplit','ledger','unit','t1','t2')

class Guards:
    def __init__(self, off=(), mut=None):
        self.off=set(off)
        self.P=dict(DEFAULTS)
        if mut: self.P.update(mut)
    def on(self,name): return name not in self.off
    def p(self,k,ctx=None):
        c=self.P.get('COND')
        if c is not None:
            v=c(k,ctx)
            if v is not None: return v
        return self.P[k]

DEFAULT_OFF=('lemmaAweak',)+UNPROVEN

def corners(B, G):
    FL=G.p('FL')
    return [(FL*d5, X4, B-d5-X4) for d5 in range(B+1) for X4 in range(B-d5+1)]

def pool_splits(Z, G):
    zqmax = min(Z,1) if G.on('ledger') else Z      # [cite: LEDGER]
    for zq in range(zqmax+1):
        r=Z-zq
        for zh in range(r+1):
            for zp3 in range(r-zh+1):
                for zp2s in range(r-zh-zp3+1):
                    yield (zq,zh,zp3,zp2s,r-zh-zp3-zp2s)

def admissible(D,X4,Z,e,pools,slack,G,exhaustive=False):
    zq,zh,zp3,zp2s,zp2g=pools
    ctx=dict(D=D,X4=X4,Z=Z,e=e,B=D//G.p('FL')+X4+Z)
    # ---- guard switches, one line each, each carrying its citation ----
    g_unit    = G.on('unit')        # [cite: UNIT]
    g_t1      = G.on('t1')          # [cite: T1]
    g_t2      = G.on('t2')          # [cite: T2]
    g_lemmaS  = G.on('lemmaS')      # [cite: LEMMAS]
    g_l12     = G.on('l12')         # [cite: L12]
    g_lu19    = G.on('lu19')        # [cite: LU19]
    g_lu8     = G.on('lu8')         # [cite: LU8]
    g_defsp   = G.on('defsplit')    # [cite: DEFSPLIT]
    g_e1sp    = G.on('e1sp')        # [cite: E1]
    g_e2sp    = G.on('e2sp')        # [cite: E2]
    g_t7      = G.on('t7')          # [cite: T7]
    g_lemmaR  = G.on('lemmaR')      # [cite: LEMMAR]
    g_e3      = G.on('e3')          # [cite: E3]
    g_lemmaC  = G.on('lemmaC')      # [cite: LEMMAC]
    g_lemmaA  = G.on('lemmaA')      # [cite: LEMMAA]
    g_lemAw   = G.on('lemmaAweak')
    g_pareto  = G.on('pareto')      # [cite: PARETO]
    g_paretos = G.on('paretos')     # [cite: PARETOS]
    g_lu15    = G.on('lu15')        # [cite: LU15]
    # ---- guard constants ----
    FL=G.p('FL',ctx); NM2=G.p('NM2',ctx); SLD=G.p('SLACKDIV',ctx)
    PNB=G.p('PNUM_BASE',ctx); UNB=G.p('UNIT_BASE',ctx); T7B=G.p('T7_BASE',ctx)
    CC=G.p('CHAINCAP',ctx); EP=G.p('ENDPEN',ctx); SP_=G.p('SINGPEN',ctx)
    L8C=G.p('LU8_COEF',ctx); L19C=G.p('LU19_COEF',ctx)
    RC_=G.p('RUNCAP',ctx); RFC=G.p('RUNFOURCAP',ctx); L15C=G.p('LU15_COEF',ctx)
    PSLOP=G.p('PARETO_SLOP',ctx); PSNS=G.p('PARETOS_NS',ctx)

    zL=zq+zh+zp2s+zp2g
    Pnum=PNB+D//FL                                      # [cite: PNUM]
    h=UNB+D//FL+Z-e
    if g_unit and h<0: return []                        # [cite: UNIT]
    cnl=e-zL
    if g_t1 and cnl<0: return []                        # [cite: T1]
    q2cap = zp2s + (slack//SLD if g_lemmaS else 10**9)  # [cite: LEMMAS]
    wits=[]
    X4h_range=[X4] if not exhaustive else range(X4+1)   # [cite: T7]
    for Q2 in range(e+1):
        if Q2>q2cap: break
        pshits=e-Q2-zp3-zp2g                            # [cite: T2]
        if g_t2 and pshits<0: break
        if g_lu19 and D < (e-Z) + L19C*max(0,Q2-3*Z): continue   # [cite: LU19]
        NcycHi = e-Q2 if g_l12 else e                   # [cite: L12]
        NcycLo=0
        if g_lu8 and Z==0:                              # [cite: LU8]
            need=6*e-L8C*Q2-D
            if need>0: NcycLo=-((-need)//L8C)
        for Ncyc in range(NcycLo,NcycHi+1):
            if g_lu8 and Z==0 and D < e + L8C*(e-Q2-Ncyc): continue   # [cite: LU8]
            for S4 in range(D//2+1):                    # [cite: DEFSPLIT]
                if g_defsp:
                    if S4==0:
                        S5range=(D,)
                    else:
                        lo=max(0,D-NM2*S4); hi=D-2*S4
                        if hi<lo: continue
                        S5range=range(lo,hi+1)
                else:
                    S5range=range(D-2*S4+1)
                for S5 in S5range:
                    Sp=S5+S4
                    if D==0 and Sp!=0: continue
                    if Sp>D: continue
                    if g_e1sp and pshits>Sp: continue    # [cite: E1]
                    if g_e2sp and cnl>Sp: continue       # [cite: E2]
                    Fp=Pnum-Sp
                    if Fp<0: continue
                    for X4h in X4h_range:
                        NChcap=(T7B+X4h+zh+cnl) if g_t7 else Pnum   # [cite: T7]
                        if g_lemmaR:                                # [cite: LEMMAR]
                            Rcap=T7B+X4h+zh+cnl+S4
                            if Fp+S5 > RC_*Rcap: continue
                            if S5 > RFC*Rcap: continue
                        NCh_range=[min(Pnum,NChcap)] if not exhaustive else range(1,min(Pnum,NChcap)+1)
                        for NCh in NCh_range:
                            if NCh>Pnum or NCh>NChcap: continue
                            SH=pshits; ST=cnl
                            if SH>NCh or ST>NCh: continue
                            OV=max(0,SH+ST-Sp) if g_e3 else 0       # [cite: E3]
                            PEN=max(OV,Ncyc-zp2g) if g_lemmaC else OV   # [cite: LEMMAC]
                            if PEN<0: PEN=0
                            if PEN>NCh: continue
                            if g_lemmaA:                            # [cite: LEMMAA]
                                if Pnum-2*D > CC*NCh - EP*(SH+ST) - SP_*PEN: continue
                            elif g_lemAw:
                                if Pnum-2*D > CC*NCh-SH-ST-3*PEN: continue
                            if g_pareto:                            # [cite: PARETO]
                                if Pnum > pareto_F(NCh,D,min(SH,NCh),min(ST,NCh),PSLOP,CC,EP): continue
                            if g_paretos:                           # [cite: PARETOS]
                                ns=PEN*PSNS
                                if D-ns<0: continue
                                if Pnum > ns + pareto_F(NCh-ns,D-ns,max(0,SH-ns),
                                                        max(0,ST-ns),PSLOP,CC,EP): continue
                            if g_lu15:                              # [cite: LU15]
                                if Fp > L15C*(1+X4+Z+Sp-max(0,e-Q2-Z)): continue
                            wits.append(dict(D=D,X4=X4,Z=Z,e=e,Q2=Q2,Ncyc=Ncyc,Sp=Sp,S5=S5,S4=S4,
                                   X4h=X4h,NCh=NCh,pools=pools,h=h,cnl=cnl,pshits=pshits,
                                   Pnum=Pnum,Fp=Fp,SH=SH,ST=ST,PEN=PEN))
                            if not exhaustive: return wits
    return wits

EHARDCAP=64   # absolute stop for the e loop; the real bound is h >= 0 (UNIT-n6)

def _erange(D,X4,Z,G,emax):
    """e runs while h = UNIT_BASE + D/5 + Z - e is still >= 0, evaluated with the
    ACTUAL (possibly mutated, possibly ctx-conditional) UNIT_BASE so that a
    weakening of the unit identity really does widen what the scanner explores."""
    if emax is not None:
        return range(max(emax,0)+1)
    FL=G.p('FL'); out=[]
    for e in range(EHARDCAP+1):
        ctx=dict(D=D,X4=X4,Z=Z,e=e,B=D//FL+X4+Z)
        if G.p('UNIT_BASE',ctx)+D//FL+Z-e < 0: break
        out.append(e)
    return out

def scan(B,slack,G,exhaustive=False,emax=None):
    res={}
    FL=G.p('FL')
    for (D,X4,Z) in corners(B,G):
        alive=[]
        for e in _erange(D,X4,Z,G,emax):
            for pools in pool_splits(Z,G):
                w=admissible(D,X4,Z,e,pools,slack,G,exhaustive)
                if w: alive.append((e,pools,w[0])); break
        res[(D,X4,Z)]=alive
    return res

def scan_length(L,G,exhaustive=False):
    T=L-725; out={}
    for B in range(1, T-G.p('THMM_CONST')+1):
        W=G.p('THMM_CONST')+B; slack=T-W
        if slack<0: continue
        out[B]=(slack, scan(B,slack,G,exhaustive))
    return out

PUBLISHED_LENGTHS=range(868,874)   # the regression box: every published number

def fine_signature(Lrange,G):
    """A STRICTLY FINER observable than the published map: for every
    (length, rung, corner, e) cell it records the first admissible witness
    profile, not merely whether the cell is alive.  A weakening that only admits
    an extra (or lexicographically earlier) witness inside an already-surviving
    cell changes this signature while leaving the published map untouched, so the
    teeth phases use it and see much more than the map alone."""
    sig=[]
    FL=G.p('FL')
    for L in Lrange:
        T=L-725
        for B in range(1,T-G.p('THMM_CONST')+1):
            W=G.p('THMM_CONST')+B; slack=T-W
            if slack<0: continue
            for (D,X4,Z) in corners(B,G):
                for e in _erange(D,X4,Z,G,None):
                    hit=None
                    for pools in pool_splits(Z,G):
                        w=admissible(D,X4,Z,e,pools,slack,G,False)
                        if w:
                            x=w[0]
                            hit=(pools,x['Q2'],x['Ncyc'],x['Sp'],x['S5'],x['S4'],x['X4h'],x['NCh'])
                            break
                    sig.append((L,B,D,X4,Z,e,hit))
    return tuple(sig)

def map_signature(Lrange,G,exhaustive=False):
    """Canonical, hashable summary of every published corner-map number."""
    sig=[]
    for L in Lrange:
        r=scan_length(L,G,exhaustive)
        for B,(sl,res) in sorted(r.items()):
            for k,v in sorted(res.items()):
                if v: sig.append((L,B,sl,k,min(e for e,_,_ in v),max(e for e,_,_ in v),len(v)))
    return tuple(sig)

if __name__=="__main__":
    G=Guards(DEFAULT_OFF)
    print("### n=6 corner map (proved guard set; LU19/LU15 excluded as unproved)")
    for L in PUBLISHED_LENGTHS:
        r=scan_length(L,G); tot=0; d=[]
        for B,(sl,res) in sorted(r.items()):
            na=sum(1 for k,v in res.items() if v); tot+=na; d.append(f"B{B}/sl{sl}:{na}")
        print(f"L={L}  surviving corners = {tot}   [{'  '.join(d)}]")
    print("\n### the length-872 habitat, corner by corner")
    for B in (1,2,3,4,5):
        res=scan(B,5-B,G)
        alive=[(k,v) for k,v in sorted(res.items()) if v]
        print(f"-- B={B} (W={142+B}, slack={5-B}): {len(res)} corners, {len(alive)} alive")
        for k,v in alive:
            es=[e for e,_,_ in v]
            print(f"     (D,X4,Z)={k}  e in {min(es)}..{max(es)}  ({len(es)} values)")
