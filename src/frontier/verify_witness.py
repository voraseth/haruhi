#!/usr/bin/env python3
"""G20-FINAL: independent verifier for the sharpness claim
"each maximum is attained by an explicitly constructed chain".

Reads the witness dump of chains871_witness (logs/witness_20.log) and checks,
from the RAW definitions of proof6.md sections 1,3,7 (re-derived here in
Python, sharing no code with the C enumerator), that each printed chain is a
genuine class-disjoint hop-chain of the stated cost/type whose block count
equals the certified table entry.

Definitions used:
  perms of [6]; rot(p)=p2p3p4p5p6p1 ; rho(p)=p2p3p4p5p1p6
  d(p,q) = 6 - (length of the longest suffix of p that is a prefix of q)
  rotation class C(p) = {rot^i p}
  seg(x,l): head crit x, classes C(rho^j x) for j<l (l in 1..5),
            end completion = rot^{-1}(rho^{l-1} x)
  chain: class-disjoint segs joined by HOPs, i.e. d(end_i, x_{i+1}) = 3
  blocks = #segs, cost = sum(5-l_i), a = [l_first<5], b = [l_last<5]
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("verify_witness: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 1 `assert` statements")
import sys, itertools


PERMS = [tuple(p) for p in itertools.permutations(range(1,7))]
IDX   = {p:i for i,p in enumerate(PERMS)}
def rot(p): return p[1:]+p[:1]
def rho(p): return p[1:5]+p[:1]+p[5:]
ROT = [IDX[rot(p)] for p in PERMS]
RHO = [IDX[rho(p)] for p in PERMS]
def cls(i):
    o=[i]; c=i
    for _ in range(5):
        c=ROT[c]; o.append(c)
    return min(o)
CLS=[cls(i) for i in range(720)]
def dist(i,j):
    p,q=PERMS[i],PERMS[j]
    for k in range(1,6):
        if p[k:]==q[:6-k]: return k
    return 6

def seg_classes(x,l):
    y=x; out=[]
    for _ in range(l):
        out.append(CLS[y]); y=RHO[y]
    return out
def seg_end(x,l):
    y=x
    for _ in range(l-1): y=RHO[y]
    for _ in range(5): y=ROT[y]
    return y

log = sys.argv[1] if len(sys.argv)>1 else "logs/witness_20.log"
table={}; wit={}; cprog={}
for line in open(log):
    t=line.split()
    if line.startswith("P "):
        cprog[int(t[1])]=tuple(int(v) for v in t[2:8])
    elif line.startswith("W "):
        c,a,b,n = int(t[1]),int(t[2]),int(t[3]),int(t[4])
        pairs=[tuple(int(v) for v in s.split("/")) for s in t[6:]]
        wit[(c,a,b)]=(n,pairs)
    elif ":" in line and line.split(":")[0].strip().isdigit():
        c=int(line.split(":")[0]); vals=[int(v) for v in line.split(":")[1].split()]
        for k,(a,b) in enumerate([(0,0),(1,0),(0,1),(1,1)]): table[(c,a,b)]=vals[k]

# index mapping cross-check: our independent perm order must match the C one
assert len(cprog)==720 and all(cprog[i]==PERMS[i] for i in range(720)), "perm index mismatch"
print("PERM-INDEX-MAP  OK (720 perms, identical order)")

ok=bad=skip=0
for (c,a,b),g in sorted(table.items()):
    if g < 0:
        skip+=1; continue
    if (c,a,b) not in wit:
        print(f"MISSING WITNESS cost={c} (a,b)=({a},{b}) g={g}"); bad+=1; continue
    n,pairs = wit[(c,a,b)]
    errs=[]
    if n!=len(pairs): errs.append("blocks/pairs mismatch")
    if n!=g: errs.append(f"blocks {n} != certified g {g}")
    used=set(); cost=0; end=None
    for k,(x,l) in enumerate(pairs):
        if not (1<=l<=5): errs.append(f"bad length {l}"); break
        cs=seg_classes(x,l)
        if len(set(cs))!=l: errs.append(f"seg {k} self-overlapping"); break
        if used & set(cs): errs.append(f"seg {k} reuses a class"); break
        used |= set(cs)
        cost += 5-l
        if k>0:
            d=dist(end,x)
            if d!=3: errs.append(f"join {k-1}->{k} has d={d}, not a HOP"); break
        end = seg_end(x,l)
    if not errs:
        if cost!=c: errs.append(f"cost {cost} != {c}")
        if (1 if pairs[0][1]<5 else 0)!=a: errs.append("first-short flag a wrong")
        if (1 if pairs[-1][1]<5 else 0)!=b: errs.append("last-short flag b wrong")
        if len(used)!=sum(l for _,l in pairs): errs.append("class accounting")
        if len(used)>120: errs.append("more than 120 classes")
    if errs:
        print(f"FAIL cost={c} (a,b)=({a},{b}) g={g}: {'; '.join(errs)}"); bad+=1
    else:
        ok+=1
print(f"WITNESS-CHECK cells_ok={ok} cells_failed={bad} cells_empty(g=-1)={skip}")
for key in [(18,0,0),(19,0,0),(20,0,0)]:
    if key in wit:
        n,pairs=wit[key]
        print(f"EXPLICIT CHAIN cost={key[0]} type(0,0) blocks={n}")
        print("  segments (head-perm, length):",
              " ".join(f"{''.join(map(str,PERMS[x]))}/{l}" for x,l in pairs))
print("VERDICT:", "SHARP - every certified maximum is attained by an explicit chain"
      if bad==0 else "SHARPNESS CHECK FAILED")
sys.exit(1 if bad else 0)
