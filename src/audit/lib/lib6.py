"""lib6.py -- n=6 structural analyzer, written from the RAW DEFINITIONS.

Definitions (n general, instantiated at n=6):
  rot(p)  = p2 p3 ... pn p1
  sig(p)  = p3 p4 ... pn p2 p1
  d(p,q)  = n - (length of longest suffix of p that is a prefix of q)
  rotation class C(p) = {rot^i p}; (n-1)! classes of size n
  first-occurrence ordering q_1..q_{n!} at positions p_1<...<p_{n!}
  gap_k = p_{k+1}-p_k, d_k = d(q_k,q_{k+1}), lead=p_1, trail=L-(p_N+n)
  W = sum (d_k - 1);  slack = lead+trail+sum(gap_k-d_k)
  run = maximal block of consecutive q_i joined by d=1 steps
  e = #runs - (n-1)!
  y_C = temporally last element of class C ; crit(C) = rot(y_C)
  completion run end: z = y_{C(z)} ; else premature
  d=2 exit typing: completion->link (landing is a crit) / CNL (non-crit)
                   premature->S-exit (landing rot^2 z) / premature-sig (landing sig z)
                       ps-hit = premature-sig whose landing is a crit
  heavy: d>=3 ; X4h = #{d>=4} ; X4 = sum_{d>=4}(d-3)
  pools zq,zh,zp3,zp2s,zp2g; Z = sum; zL = zq+zh+zp2s+zp2g
  link B->C if B's completion exit is a link landing on crit(C)
  link-paths; deficiency (n-1)-l ; D = total deficiency; P#=#paths; S_p=#short
  hop: path-end completion d=3 exit landing exactly on another path's head crit
  hop-chains; blocks, cost, value = blocks-2*cost; NCh, Ns, SH, ST
  pointer graph: vertices=runs; each d=2 transition from run end z gives edge
      run starting at rot(z) -> run starting at the landing; S-exits give NO edge
  Ncyc = #cycles of the pointer graph
NO code imported from any other approach directory.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("lib6: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 47 `assert` statements")
import sys, itertools
from collections import defaultdict

class Ordering:
    def __init__(self, n, seq, positions=None, L=None):
        self.n = n
        self.N = 1
        for i in range(2, n+1): self.N *= i
        self.seq = [tuple(p) for p in seq]
        assert len(self.seq) == self.N, (len(self.seq), self.N)
        assert len(set(self.seq)) == self.N, "ordering must be a permutation of S_n"
        self.pos_of = {p:i for i,p in enumerate(self.seq)}
        self.positions = positions
        self.L = L
        self._compute()

    # ---- primitives ----
    def rot(self, p):  return p[1:] + p[:1]
    def sig(self, p):  return p[2:] + (p[1], p[0])
    def d(self, p, q):
        n = self.n
        for k in range(1, n+1):          # overlap length n-k
            if p[k:] == q[:n-k]: return k
        return n

    def _compute(self):
        n, N, seq = self.n, self.N, self.seq
        self.dk = [self.d(seq[k], seq[k+1]) for k in range(N-1)]
        self.W = sum(x-1 for x in self.dk)
        # slack (only if positions given)
        if self.positions is not None:
            gp = self.positions
            assert len(gp) == N and all(gp[i] < gp[i+1] for i in range(N-1))
            self.lead = gp[0]; self.trail = self.L - (gp[-1] + n)
            self.gaps = [gp[k+1]-gp[k] for k in range(N-1)]
            assert all(self.gaps[k] >= self.dk[k] for k in range(N-1)), "gap<d"
            self.slack = self.lead + self.trail + sum(self.gaps[k]-self.dk[k] for k in range(N-1))
            # A19-T0 identity
            assert self.L == n + (N-1) + self.W + self.slack, "slack identity"
        else:
            self.lead = self.trail = self.slack = None

        # classes
        cls = {}
        cid = 0
        for p in itertools.permutations(range(1, n+1)):
            p = tuple(p)
            if p in cls: continue
            x = p
            for _ in range(n):
                cls[x] = cid; x = self.rot(x)
            cid += 1
        self.cls = cls; self.nclass = cid
        assert cid == N // n

        # runs: maximal blocks joined by d=1
        runs = []; cur = [0]
        for k in range(N-1):
            if self.dk[k] == 1: cur.append(k+1)
            else: runs.append(cur); cur = [k+1]
        runs.append(cur)
        self.runs = runs
        self.nruns = len(runs)
        self.e = self.nruns - self.nclass
        self.run_of = {}
        for ri,r in enumerate(runs):
            for i in r: self.run_of[i] = ri
        # transitions = steps with d>=2 (between runs)
        self.trans = [k for k in range(N-1) if self.dk[k] >= 2]
        assert len(self.trans) == self.nruns - 1

        # completions
        last_in_class = {}
        for i,p in enumerate(seq): last_in_class[cls[p]] = i
        self.y = {c: seq[i] for c,i in last_in_class.items()}
        self.crit = {c: self.rot(self.y[c]) for c in self.y}
        self.crit_set = {self.crit[c]: c for c in self.crit}
        assert len(self.crit_set) == self.nclass
        # run ends / starts
        self.run_end_idx = [r[-1] for r in runs]
        self.run_start_idx = [r[0] for r in runs]
        self.is_completion_end = []
        ncomp = 0; nprem = 0
        for r in runs:
            z = seq[r[-1]]
            isc = (z == self.y[cls[z]])
            self.is_completion_end.append(isc)
            ncomp += isc; nprem += (not isc)
        assert ncomp == self.nclass, (ncomp, self.nclass)   # Prop 1(b)
        assert nprem == self.e
        # run starts: crits + nc
        self.nc_runs = [ri for ri,r in enumerate(runs) if seq[r[0]] not in self.crit_set]
        assert len(self.nc_runs) == self.e, (len(self.nc_runs), self.e)  # Prop 1(c)

        self.h = 0; self.X4 = 0; self.X4h = 0
        self.zq = 0 if seq[0] in self.crit_set else 1
        self.zh = self.zp3 = self.zp2s = self.zp2g = 0
        self.cnl = 0; self.pshits = 0; self.Q2 = 0; self.PS = 0
        self.links = {}        # class -> class
        self.hop_src = {}      # source path-end class -> landing class (filled later)
        self.d2_edges = []     # (tail_run, head_run) pointer edges
        self.heavy_land = []
        for k in self.trans:
            z = seq[k]; t = seq[k+1]; dd = self.dk[k]
            cz = cls[z]
            comp = (z == self.y[cz])
            land_is_crit = t in self.crit_set
            if dd >= 3:
                self.h += 1
                if dd >= 4: self.X4h += 1; self.X4 += dd-3
                if not land_is_crit: self.zh += 1
                if not comp: self.zp3 += 1
                self.heavy_land.append((k, comp, dd, land_is_crit))
            else:  # dd == 2
                assert t == self.rot(self.rot(z)) or t == self.sig(z)   # Prop 1(d)
                tail_run = self.run_of[self.pos_of[self.rot(z)]]
                head_run = self.run_of[k+1]
                if comp:
                    assert t == self.sig(z)                              # Prop 1(e)
                    if land_is_crit:
                        self.links[cz] = self.crit_set[t]
                    else:
                        self.cnl += 1
                    self.d2_edges.append((tail_run, head_run))
                else:
                    if t == self.rot(self.rot(z)):
                        self.Q2 += 1
                        if not land_is_crit: self.zp2s += 1
                        # S-exits contribute NO pointer edge
                    else:
                        self.PS += 1
                        if land_is_crit: self.pshits += 1
                        else: self.zp2g += 1
                        self.d2_edges.append((tail_run, head_run))
        self.Z = self.zq + self.zh + self.zp3 + self.zp2s + self.zp2g
        self.zL = self.zq + self.zh + self.zp2s + self.zp2g
        self.Q2hits = self.Q2 - self.zp2s

        # ---- link paths ----
        indeg = defaultdict(int)
        for a,b in self.links.items(): indeg[b] += 1
        assert all(v <= 1 for v in indeg.values())
        heads = [c for c in range(self.nclass) if indeg[c] == 0]
        self.paths = []
        seen = set()
        for hc in heads:
            path = [hc]; seen.add(hc)
            while path[-1] in self.links:
                nxt = self.links[path[-1]]
                assert nxt not in seen, "link cycle"
                path.append(nxt); seen.add(nxt)
            self.paths.append(path)
        assert len(seen) == self.nclass, "link cycle present"
        self.Pnum = len(self.paths)
        full_len = n-1
        assert all(len(p) <= full_len for p in self.paths), \
            "path longer than n-1: "+str(max(len(p) for p in self.paths))
        self.D = sum(full_len - len(p) for p in self.paths)
        self.S_p = sum(1 for p in self.paths if len(p) < full_len)
        assert full_len*self.Pnum - self.nclass == self.D
        assert self.Pnum == self.nclass//full_len + self.D//full_len

        # ---- hop chains ----
        self.path_of = {}
        for pi,p in enumerate(self.paths):
            for c in p: self.path_of[c] = pi
        head_crit_to_path = {self.crit[p[0]]: pi for pi,p in enumerate(self.paths)}
        hops = {}   # path -> path
        for k in self.trans:
            z = seq[k]; t = seq[k+1]; dd = self.dk[k]
            if dd != 3: continue
            cz = cls[z]
            if z != self.y[cz]: continue            # must be a completion
            pi = self.path_of[cz]
            if self.paths[pi][-1] != cz: continue   # must be the path END
            if t in head_crit_to_path:
                pj = head_crit_to_path[t]
                if pj != pi:
                    hops[pi] = pj
        hindeg = defaultdict(int)
        for a,b in hops.items(): hindeg[b] += 1
        assert all(v <= 1 for v in hindeg.values())
        chain_heads = [pi for pi in range(self.Pnum) if hindeg[pi] == 0]
        self.chains = []
        seen2 = set()
        for ch in chain_heads:
            c = [ch]; seen2.add(ch)
            while c[-1] in hops:
                nx = hops[c[-1]]
                assert nx not in seen2, "hop cycle"
                c.append(nx); seen2.add(nx)
            self.chains.append(c)
        assert len(seen2) == self.Pnum, "hop cycle present"
        self.NCh = len(self.chains)
        self.SH = sum(1 for c in self.chains if len(self.paths[c[0]]) < full_len)
        self.ST = sum(1 for c in self.chains if len(self.paths[c[-1]]) < full_len)
        self.Ns = sum(1 for c in self.chains if len(c)==1 and len(self.paths[c[0]])<full_len)
        self.chain_stats = []
        for c in self.chains:
            blocks = len(c)
            cost = sum(full_len-len(self.paths[pi]) for pi in c if len(self.paths[pi])<full_len)
            self.chain_stats.append((blocks, cost, blocks-2*cost,
                                     len(self.paths[c[0]])<full_len,
                                     len(self.paths[c[-1]])<full_len))
        self.Sigma = sum(v for _,_,v,_,_ in self.chain_stats)

        # ---- pointer graph ----
        out = {}; inn = {}
        for a,b in self.d2_edges:
            assert a not in out, "pointer out-degree > 1"
            assert b not in inn, "pointer in-degree > 1"
            out[a] = b; inn[b] = a
        self.Ncyc = 0
        vis = set()
        for v in range(self.nruns):
            if v in vis: continue
            # walk back to a start or detect cycle
            path = []; u = v; loc = {}
            while u is not None and u not in vis and u not in loc:
                loc[u] = len(path); path.append(u)
                u = inn.get(u)
            if u is not None and u in loc:
                self.Ncyc += 1
            for x in path: vis.add(x)

        # ---- identities (Prop 1) ----
        self.check_identities()

    def check_identities(self):
        n = self.n; fl = n-1
        # (g) T1
        assert self.cnl == self.e - self.zL, ("T1", self.cnl, self.e, self.zL)
        # T2
        assert self.pshits == self.e - self.Q2 - self.zp3 - self.zp2g, "T2"
        # (h) ledger
        assert self.e + self.h + 1 - self.Pnum == self.Z, ("ledger", self.e,self.h,self.Pnum,self.Z)
        # unit identity  h = (nclass-1) + D/fl + Z - e
        assert self.Pnum == self.nclass//fl + self.D//fl, "P# identity"
        assert self.h == self.Pnum - 1 + self.Z - self.e, "unit identity"
        # exact re-derivation: W = t2 + X4 + 2h, t2 = ntrans - h
        ntr = self.nruns-1
        assert self.W == (ntr - self.h) + self.X4 + 2*self.h
        # => W = ntr + h + X4 = (nclass-1+e) + h + X4
        assert self.W == (self.nclass-1) + self.e + self.h + self.X4
        # Theorem M form
        assert self.W == (self.nclass-1) + (self.nclass//fl - 1) + self.D//fl + self.X4 + self.Z, "TheoremM"
        # (A0)
        assert self.Pnum - 2*self.D == self.Sigma, "A0"
        # L12  Ncyc + Q2 <= e
        assert self.Ncyc + self.Q2 <= self.e, ("L12", self.Ncyc, self.Q2, self.e)
        # E1'/E2'/E3'
        assert self.SH >= self.pshits, "E1'"
        assert self.ST >= self.cnl, "E2'"
        assert self.pshits <= min(self.SH, self.S_p), "E1' Sp"
        assert self.cnl <= min(self.ST, self.S_p), "E2' Sp"
        assert self.Ns >= max(0, self.pshits + self.cnl - self.S_p), "E3'"
        # Lemma C
        assert self.Ns >= self.Ncyc - self.zp2g, ("LemmaC", self.Ns, self.Ncyc, self.zp2g)
        # T7
        assert self.NCh <= 1 + self.X4h + self.zh + self.cnl, ("T7", self.NCh, self.X4h, self.zh, self.cnl)
        # X4h <= X4
        assert self.X4h <= self.X4
        # S_p bounds
        assert self.S_p <= self.D
        if self.D > 0: assert self.S_p >= -(-self.D//(fl-1))    # ceil(D/(n-2))
        # Lemma S (slack-parametric): Q2 - zp2s <= floor(interior slack/(n-2))
        if self.slack is not None:
            j0 = self.slack - self.lead - self.trail
            assert self.Q2 - self.zp2s <= j0//(n-2), ("LemmaS", self.Q2, self.zp2s, j0)
        # L-U8 (Z=0)
        if self.Z == 0:
            assert self.D >= self.e + fl*(self.e - self.Q2 - self.Ncyc), "L-U8"
        # L-U19 general: D >= (e-Z) + fl*max(0, Q2 - 3Z)
        assert self.D >= (self.e - self.Z) + fl*max(0, self.Q2 - 3*self.Z), "L-U19"
        return True

    def summary(self):
        return dict(L=self.L, W=self.W, slack=self.slack, lead=self.lead, trail=self.trail,
                    e=self.e, D=self.D, X4=self.X4, X4h=self.X4h, Z=self.Z,
                    zq=self.zq, zh=self.zh, zp3=self.zp3, zp2s=self.zp2s, zp2g=self.zp2g,
                    Q2=self.Q2, PS=self.PS, cnl=self.cnl, pshits=self.pshits,
                    Pnum=self.Pnum, S_p=self.S_p, h=self.h, NCh=self.NCh,
                    SH=self.SH, ST=self.ST, Ns=self.Ns, Ncyc=self.Ncyc, Sigma=self.Sigma,
                    nruns=self.nruns)

def from_string(s, n=6):
    s = ''.join(ch for ch in s if ch.isdigit())
    L = len(s)
    seen = {}
    order = []; positions = []
    for i in range(L-n+1):
        w = tuple(int(c) for c in s[i:i+n])
        if len(set(w)) == n and w not in seen:
            seen[w] = i; order.append(w); positions.append(i)
    return Ordering(n, order, positions, L)

if __name__ == "__main__":
    o = from_string(open(sys.argv[1]).read(), int(sys.argv[2]) if len(sys.argv)>2 else 6)
    for k,v in o.summary().items(): print(f"{k}={v}")
    print("chain_stats(blocks,cost,value,shortfirst,shortlast):", o.chain_stats)
