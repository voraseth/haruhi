#!/usr/bin/env python3
"""Independent (Python) check of abstract-chain witnesses against the paper's
definitions: rot, rho, C(.), segment class occupancy, cost-3 hops, cost, type."""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("check_witness: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 1 `assert` statements")
import sys, re
from itertools import permutations


def rot(p):  return p[1:]+p[:1]
def rinv(p): return p[-1:]+p[:-1]
def rho(p):  return p[1:5]+p[0:1]+p[5:6]
def cls(p):
    o=[]; q=p
    for _ in range(6): o.append(q); q=rot(q)
    return min(o)
def d(p,q):
    assert p!=q
    for k in range(5,0,-1):
        if p[6-k:]==q[:k]: return 6-k
    return 6

def check(c,a,b,blocks,lens,heads):
    errs=[]
    if heads[0]!=(1,2,3,4,5,6): errs.append("head not 123456")
    if len(lens)!=blocks or len(heads)!=blocks: errs.append("length mismatch")
    used={}
    for i,(x,l) in enumerate(zip(heads,lens)):
        q=x
        for j in range(l):
            cc=cls(q)
            if cc in used: errs.append(f"class reuse seg{i} pos{j} (also seg{used[cc]})")
            used[cc]=i
            q=rho(q)
        # completion = rot^{-1}(rho^{l-1} x)
        end = rinv(rho_pow(x,l-1))
        if i+1<blocks:
            dd=d(end,heads[i+1])
            if dd!=3: errs.append(f"transition {i}->{i+1} has cost {dd}, not 3")
    cost=sum(5-l for l in lens)
    if cost!=c: errs.append(f"cost {cost} != {c}")
    if (1 if lens[0]<5 else 0)!=a: errs.append("a mismatch")
    if (1 if lens[-1]<5 else 0)!=b: errs.append("b mismatch")
    if len(used)!=sum(lens): errs.append("class count mismatch")
    return errs, cost, len(used)

def rho_pow(x,k):
    for _ in range(k): x=rho(x)
    return x

pat=re.compile(r"W c=(\d+) a=(\d+) b=(\d+) blocks=(\d+) lens=(\S+) heads=(\S+)")
ok=True
for line in open(sys.argv[1]):
    m=pat.match(line.strip())
    if not m: continue
    c,a,b,blocks=int(m.group(1)),int(m.group(2)),int(m.group(3)),int(m.group(4))
    lens=[int(ch) for ch in m.group(5)]
    heads=[tuple(int(ch) for ch in w) for w in m.group(6).strip(',').split(',')]
    errs,cost,ncl=check(c,a,b,blocks,lens,heads)
    status="OK " if not errs else "FAIL"
    if errs: ok=False
    print(f"{status} c={c} a={a} b={b} blocks={blocks} cost={cost} classes_used={ncl}"
          + ("" if not errs else "  "+ "; ".join(errs)))
print("ALL WITNESSES VALID" if ok else "WITNESS FAILURES")
