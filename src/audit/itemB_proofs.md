# itemB_proofs.md — proofs of Algorithm 2's rejection rules R1-R14
All from raw n=6 definitions (720 permutations of [6]; rot, sig, rho; d(p,q) =
6 - |longest suffix of p that is a prefix of q|; 120 rotation classes; rho of
order 5, 144 rho-orbits; first-occurrence ordering q_1..q_720; runs = maximal
d=1 blocks, e = #runs-120; y_C = temporally last element of class C,
crit(C)=rot(y_C); transition typing and pools zq,zh,zp3,zp2s,zp2g as in
proof6.md §1). "The ordering" always means an arbitrary first-occurrence
ordering of an arbitrary superpermutation of the scanned length; nothing is
assumed about it.

## Preliminaries used repeatedly (all proved in proof6.md §2-§3; reproduced)

P0 (Prop 1). (a) crit(C) is a run start: else the element before rot(y_C) in
its run would be y_C, so y_C would be immediately followed by rot(y_C) in the
ordering, i.e. rot(y_C) occurs later than y_C in C — contradicting y_C last.
(b) #runs = 120+e with exactly 120 completion run ends (each class contributes
exactly one, y_C; the run containing y_C cannot continue since the continuation
is rot(y_C), later in C) and e premature ends. (c) run starts = 120 crits + e
non-crit ("nc") starts. (d) d=2 dichotomy: d(z,t)=2 forces t = rot^2(z) or
sig(z) (last 4 letters of z are first 4 of t; two ways to finish). (e) a
completion d=2 exit lands on sig(y_C) (rot^2(y_C) is in C, already visited,
not a first occurrence). (f) every d=2 landing and rot(z) for premature z are
run starts.

P1 (T1-n6). cnl = e - (zq+zh+zp2s+zp2g). Proof: count the e nc-run starts:
each is q_1 (iff q_1 not a crit: zq) or the landing of its unique entering
transition, and a transition lands on a non-crit in exactly the typed ways
CNL / S-exit-to-noncrit / premature-sig-to-noncrit / heavy-to-noncrit, counted
by cnl, zp2s, zp2g, zh.

P2 (T2-n6). pshits = e - Q2 - zp3 - zp2g. Proof: each of the e premature run
ends exits exactly once, as an S-exit (Q2), a heavy (zp3), or a premature-sig
exit; the premature-sig exits land on a non-crit (zp2g) or a crit (pshits).

P3 (L1 + L1a + PNUM). Along a link-path crit(v_{i+1}) = rho(crit(v_i))
(landing = sig(y_{v_i}) by P0(e), y_{v_i} = rot^{-1}(crit(v_i)),
sig(rot^{-1}(x)) = rho(x) by direct word computation); rho has order 5 so
l <= 5. The link relation is acyclic (pos(y_B) < pos(y_C) when B links to C:
the landing rot(y_C) is the next first occurrence and precedes y_C in C), so
the 120 classes partition into directed link-paths; D = sum(5-l) = 5*P# - 120,
i.e. P# = 24 + D/5. The same order argument makes the hop relation acyclic, so
paths partition into hop-chains.

P4 (L2). Every pointer edge advances the run start by rho (completion d=2 exit:
tail run starts rot(y_B)=crit(B), head starts sig(y_B)=rho(crit(B));
premature-sig exit from z: tail starts rot(z), head sig(z)=rho(rot(z))); rho
has order 5 and run starts are distinct permutations, and pointer in/out-degrees
are <= 1, so every pointer component is a directed path or cycle with at most
5 vertices.

## R1: h >= 0 — verdict (a) PROVED
h counts transitions with d >= 3, so h >= 0 by definition. The scanner computes
h = 23 + D/5 + Z - e, so R1 is the claim that this expression is the true h
(UNIT-n6). Derivation: exactly 119 completions have an exit (q_720 is a
completion with none); each is a link, a CNL, or heavy; #links = 120 - P#
(a class is link-entered iff not a path head, and heads number P#). So
completion heavies = 119 - (120-P#) - cnl = P# - 1 - cnl, and with the zp3
premature heavies h = P# - 1 - cnl + zp3. Substituting P# = 24 + D/5 (P3) and
cnl = e - zL (P1) with zL + zp3 = Z gives h = 23 + D/5 + Z - e. Hence rejecting
profiles with 23 + D/5 + Z - e < 0 rejects no real ordering. QED.
Dependencies: P0, P1, P3. Control: on the verified 872 (D=25,Z=0,e=25):
h = 23+5+0-25 = 3 >= 0. On the 873s (D=0,Z=0,e=0): h = 23 >= 0.

## R2: cnl >= 0 — verdict (a) PROVED
The scanner sets cnl := e - (zq+zh+zp2s+zp2g) and rejects if negative. By P1
this expression equals the number of CNLs, a cardinality, hence >= 0 in every
ordering. QED. Dependencies: P0, P1. Control: 872: cnl = 25-0 = 25 >= 0;
873s: cnl = 0.

## R3: hits >= 0 — verdict (a) PROVED
The scanner sets hits := e - Q2 - zp3 - zp2g. By P2 this equals pshits, a
cardinality, hence >= 0. QED. Dependencies: P0, P2. Control: 872:
hits = 25 - Q2; the real 872 has Q2 = 0 (slack ledger, §10a), hits = 25 >= 0.
873s: 0.

## R4: Q2 <= zp2s + floor(slack/4) — verdict (a) PROVED (re-entry bound)
Reproduced from LEMMAS-n6 (proof6.md §5), which proves the STRONGER
Q2 - zp2s <= floor((slack - lead - trail)/4); R4 follows since
lead, trail >= 0.
Proof. Slack identity (T0-n6): L = 725 + W + slack with
slack = lead + trail + sum_k(gap_k - d_k) and gap_k >= d_k for every k
(windows at p_k and p_k + gap_k overlap in 6 - gap_k positions when gap_k < 6,
so d_k <= gap_k; if gap_k >= 6 then d_k <= 6 <= gap_k). Gap dichotomy: if
d_k < gap_k < 6, the word u = (last 6-d_k letters of q_k) = (first 6-d_k
letters of q_{k+1}) would have period gap_k - d_k < |u| while having distinct
letters — impossible; so gap_k = d_k or gap_k - d_k >= 6 - d_k.
Now let z = q_k be an S-exit source: premature run end, d_k = 2, landing
q_{k+1} = rot^2(z). By the dichotomy either gap_k - d_k >= 6 - 2 = 4 (this
S-exit alone consumes >= 4 units of interior slack, and distinct S-exits are
distinct k, so the consumptions add), or gap_k = 2. In the latter case the
window at position p_k + 1 is rot(z), a permutation lying strictly between the
first occurrences of q_k and q_{k+1}; it is not a first occurrence (the next
first occurrence is q_{k+1} = rot^2(z) != rot(z)), so pos(rot(z)) < p_k, i.e.
rot(z) occurred before z. The landing rot^2(z) is a crit iff
rot^2(z) = rot(y_{C(z)}) iff rot(z) = y_{C(z)}; but pos(rot(z)) < pos(z) shows
rot(z) is not temporally last in C(z), so rot(z) != y_{C(z)} and the landing is
a NON-crit: this S-exit is counted by zp2s. Hence every S-exit outside zp2s
consumes >= 4 units of interior slack <= slack, giving
Q2 - zp2s <= floor(slack/4). QED.
Quantification: over ALL orderings of all superpermutations at the scanned
length (slack is determined by L and W: slack = L - 725 - W). No survivorship
assumption anywhere. Dependencies: T0-n6 and word combinatorics only.
Control: verified 872 has slack ledger with Q2 = zp2s = 0 (proof6.md §10a,
equality); 873s (slack=0): Q2 = 0 <= 0. Pass.

## R5: Ncyc <= e - Q2 — verdict (a) PROVED (cycle bound)
Reproduced from L12-n6 (proof6.md §6).
Proof. Let z be any premature d=2 exit source (S-exit or premature-sig exit).
rot(z) is a run start (P0(f)) and a NON-crit start: rot(z) is in C(z), the only
crit of C(z) is rot(y_{C(z)}), and rot(z) = rot(y_{C(z)}) would force
z = y_{C(z)}, contradicting premature. Distinct such z give distinct rot(z),
hence distinct nc-runs; there are e nc-runs (P0(c)).
(i) Each of the Q2 S-exits marks one nc-run this way, and an S-exit contributes
no pointer edge, so that nc-run has no pointer out-edge (its unique d=2 exit
generated none, and pointer out-edges of a run come only from the d=2 exit of
its end... precisely: the tail of any pointer edge is the run starting at
rot(z') for the exit source z', and each run is tail of at most one edge); a
vertex on a pointer cycle has out-degree 1 inside the cycle, so this nc-run
lies on no cycle.
(ii) Every pointer cycle contains at least one nc-run: a cycle with no crit-run
consists of vertices that are all nc-runs (trivially contains one); a cycle
containing a crit-run contains the full crit-chain of that crit's link-path
(links are pointer edges, in/out-degrees <= 1) and the edge leaving the chain's
last crit-run is a completion d=2 exit landing on a non-crit (it cannot be a
link: the path ended), i.e. a CNL, whose head is an nc-run in the cycle.
Cycles are vertex-disjoint, so they use Ncyc distinct nc-runs, none of them
marked by an S-exit (by (i)). Hence Q2 + Ncyc <= e. QED.
Dependencies: P0, P4 (structure of pointer graph); the classification of
cycle-internal edges (part of LEMMAC-n6's proof, itself independent of L12 —
no circularity). Control: 872 has Ncyc = 0, Q2 = 0, e = 25; 873s have
e = 0 = Ncyc = Q2. Pass.

## R6: at Z=0, D >= e + 5(e - Q2 - Ncyc) — verdict (a) PROVED (glue bound)
Reproduced from LU8-n6 (proof6.md §6). The scanner applies it ONLY at Z = 0,
matching the lemma's hypothesis (checked in scan871.py).
Proof. Assume Z = 0: zq = zh = zp3 = zp2s = zp2g = 0, so cnl = e (P1).
Step 1: every nc-run lies in a component containing a crit-run. Its start is
q_1 (impossible: zq=0 makes q_1 a crit) or the landing of exactly one
transition; that transition lands on a non-crit, so it is not heavy (zh=0),
not an S-exit landing non-crit (zp2s=0), not a premature-sig landing non-crit
(zp2g=0), and not a link (links land on crits): it is a CNL, whose pointer edge
has tail crit-run(B) for the emitting class B — same component.
Step 2: fix a component i with m_i link-paths' crit-chains inside and k_i
nc-runs. Crit-chains lie wholly inside their component (links are pointer
edges), crit-runs of different paths are disjoint, and by P4 the component has
<= 5 vertices, so sum_j l_j + k_i <= 5 and its deficiency contribution is
Def_i = 5 m_i - sum_j l_j >= 5 m_i - (5 - k_i) = k_i + 5(m_i - 1). Every
component has m_i >= 1 (a crit-run belongs to some crit-chain; an nc-run's
component contains a crit-run by Step 1).
Step 3: V = 120 + e; E = #links + #CNL + #premature-sig edges =
(120 - P#) + e + (e - Q2) at Z = 0 (the e premature ends split as Q2 S-exits
and e - Q2 premature-sig exits, zp3 = 0). Components are paths or cycles, so
#path components = V - E and Ncomp = V - E + Ncyc = P# - e + Q2 + Ncyc.
Summing Step 2 over the Ncomp components with sum m_i = P#, sum k_i = e:
D >= e + 5(P# - Ncomp) = e + 5(e - Q2 - Ncyc). QED.
Dependencies: P0, P1, P3, P4. Control: the scanner quantifies over ALL values
of Ncyc allowed by R5, and an object is a control-pass iff ITS OWN profile
passes. The verified 872 (Z=0, D=25, e=25, Q2=0) has Ncyc = 25: its pointer
graph decomposes into 25 cycles (one per nc-run, matching PEN = 25 and the
PARETOS equality 25 + F(1,0,0,0) = 29 = P# recorded in proof6.md §8/§10a), so
R6 reads D = 25 >= 25 + 5*(25 - 0 - 25) = 25 — equality, pass. The 873s have
Z=0, D=0, e=0: 0 >= 0. Pass. (Machine confirmation in
logs/itemB_controls.log.)

## R7: max(0, D-4*S4) <= S5 <= D-2*S4; Sp <= D; Sp=0 if D=0 — (a) PROVED
From DEFSPLIT-n6 (immediate from definitions): D = S5*1 + sum over the S4
paths of (5 - l) with l <= 3, so each of the S4 terms lies in {2,3,4}
(l >= 1 gives 5-l <= 4; l <= 3 gives 5-l >= 2). Hence
D - S5 = sum of S4 terms, so 2*S4 <= D - S5 <= 4*S4, i.e.
D - 4*S4 <= S5 <= D - 2*S4, and S5 >= 0 always. Sp = S5 + S4 <= S5 + (D-S5)/2
<= D (each short path contributes >= 1 to D). If D = 0 every path is full
(deficiency 0 forces l = 5 for all, as contributions are >= 1 for short), so
Sp = 0. QED. Dependencies: P3 (l <= 5). Control: 872 has (S5,S4) with
D = 25; its profile satisfies the window by §10a; 873s have D = 0 = Sp. Pass.

## R8: hits <= Sp and cnl <= Sp — verdict (a) PROVED (endpoint inequalities)
From E1-n6 and E2-n6 (proof6.md §6), reproduced.
E1 (hits <= Sp): let t be a ps-hit with landing w = crit(C'). w is a run start
(P0(a)) whose unique entering transition is t; a link is a COMPLETION d=2 exit
landing on a crit, and t is premature, so C' is not link-entered and heads its
link-path pi. pi is SHORT: were pi full, its crit-chain would be a 5-vertex
pointer component (its 4 links are pointer edges, degrees <= 1); the extra
in-edge t at crit-run(v_1) would give 6 vertices, contradicting P4 — except if
t's edge came from crit-run(v_5) itself, but then the source z would satisfy
rot(z) = crit(v_5), i.e. z = y_{v_5}, a completion, contradicting t premature.
Distinct ps-hits land on distinct crits, hence give distinct SHORT paths: the
number of ps-hits is at most Sp. By P2, hits (the scanner's derived quantity)
equals pshits. E2 (cnl <= Sp): a CNL from y_B means B has no out-link, so B
ends its path pi; a full path's end completion exits with d >= 3 or is the
global end (same 5-component argument at the other end: a full path's end
completion d=2 exit would extend the 5-vertex component), so pi is short;
distinct CNLs come from distinct classes B, giving distinct short paths. QED.
Dependencies: P0, P2, P4. Control: 872: hits = 25, cnl = 25, Sp = 25 —
equality (the 25 singleton length-4 paths are each ps-entered and
CNL-emitting); 873s: 0 <= 0. Pass.

## R9: NCh <= 1 + X4h + zh + cnl; SH <= NCh; ST <= NCh — verdict (a) PROVED
Part 1 is T7-n6 (proof6.md §6), reproduced. A hop-chain head is a link-path
whose head crit w is not hop-entered. w's entry (unique, unless w = q_1) is:
q_1 itself (possible only if q_1 is a crit: at most 1 - zq occurrences); a
d >= 4 transition (at most X4h); a completion d = 3 exit — but then the exiting
class has no out-link, so it is a path end, and a path-end completion d=3 exit
landing on a path head crit is by definition a hop, excluded (the degenerate
self-hop is excluded by hop acyclicity, P3); a premature d = 3 exit landing on
a crit (at most zp3 - zh_p where zh_p = #premature heavies landing non-crit);
a link — excluded (w would not head a path); a premature d = 2 exit: a ps-hit
(pshits) or an S-exit landing on a crit (at most Q2 - zp2s). Summing and
substituting P2 (pshits = e - Q2 - zp3 - zp2g) and P1:
NCh <= (1-zq) + X4h + (zp3 - zh_p) + (e - Q2 - zp3 - zp2g) + (Q2 - zp2s)
    = 1 + X4h + (e - zq - zp2s - zp2g) - zh_p
    = 1 + X4h + cnl + (zh - zh_p) ... wait: cnl = e - zq - zh - zp2s - zp2g,
so e - zq - zp2s - zp2g = cnl + zh, giving
NCh <= 1 + X4h + cnl + zh - zh_p <= 1 + X4h + zh + cnl. QED.
Part 2: the scanner sets SH := hits = pshits and ST := cnl. By E1 each ps-hit
heads a DISTINCT hop-chain (its path heads its chain: pi is not hop-entered
since a hop has d = 3 while t has d = 2, and distinct ps-hits give distinct
chains), so pshits <= NCh; by E2 each CNL ends a distinct chain, so
cnl <= NCh. QED.
SOUNDNESS OF THE SUBSTITUTION SH := pshits, ST := cnl (audit point): the true
quantities SH*, ST* (#chains with short first / last path) satisfy
SH* >= pshits, ST* >= cnl (E1/E2). Every use of SH, ST in R9-R13 is
monotone-safe under replacing the true value by this lower bound: R9's
SH <= NCh weakens; R11's OV = max(0, SH+ST-Sp) shrinks, so PEN shrinks, so
PEN <= NCh weakens; R12's RHS 4NCh - 2(SH+ST) - PEN grows; R13's frontier
obligations (at least SH short-first, ST short-last, PEN singletons) weaken.
A weaker test rejects fewer profiles, so no real ordering is rejected. (This
direction-check is the audit's own; the artifacts state SH >= pshits
explicitly and the scanner cites it.)
Dependencies: P0-P3, E1, E2. Control: 872: NCh = 26 = 1 + 0 + 0 + 25
(equality); SH = ST = 25 <= 26. 873s: NCh = 6 <= 1 + X4h + 0 + 0 with
X4h = 5 (six d=4 transitions? X4 = 6, X4h = 5 per proof6.md calibration:
1 + 5 + 0 + 0 = 6 = NCh, equality). Pass.

## R10: Fp + S5 <= 4*Rcap, S5 <= 2*Rcap, Rcap = 1+X4h+zh+cnl+S4 — (a)+(b)
From LEMMAR-n6 (proof6.md §8), reproduced, on top of the FINITE CHECK C6-A.
C6-A (finite check, classified (b)): every hop-chain all of whose link-paths
have length in {4,5} has at most 4 paths, at most 2 of length 4, and no
length-4 path interior. Range and sufficiency: a chain is a sequence of
pairwise class-disjoint segments over the 720 permutations joined by d=3 hops
(this is the DEFINITION of a hop-chain unfolded via L1 and P0(b): head crit x,
classes C(rho^j x) j < l, end completion rot^{-1}(rho^{l-1} x)); segments
consume disjoint classes out of 120, so every chain is a finite object, and
the DFS enumerates all of them from every possible head — WLOG head 123456 for
the cap search since relabelling the alphabet is a letterwise bijection
commuting with rot, rho, sig and d and acts transitively on the 720
permutations (so every chain is isomorphic to one with head 123456), AND
mode A was additionally re-run over all 720 heads, removing even the need for
the WLOG. No ordering falls outside the range because the caps quantify over
chains, and every chain that occurs in any ordering is a chain of this
abstract kind: the abstract enumeration is a SUPERSET of realizable chains
(only class-disjointness, L1-structure and d=3 hops are imposed — all proved
necessary conditions). Independent reimplementation: chain6.c (T-n6) and
chains871.c (T-n6-871, shares no code) agree entry for entry; RUNCAP4 PASS in
both logs.
LEMMAR (proved): each maximal {4,5}-run of link-paths (inside the global chain
decomposition) is itself a hop-chain of {4,5}-paths (a contiguous subsequence
of a chain is a chain), so C6-A caps it at 4 paths with at most 2 of length 4;
summing over the R maximal runs: Fp + S5 <= 4R and S5 <= 2R. A maximal run
ends only at: the global end of the ordering (<= 1), a d >= 4 exit (<= X4h), a
heavy landing on a non-crit (<= zh), a CNL exit (<= cnl), or a hop onto the
head of a path of length <= 3 (<= S4, distinct heads); these exhaust the ways
the run can stop, and each terminator is used by at most one run, so
R <= 1 + X4h + zh + cnl + S4 = Rcap. Substituting the cap for R (the bounds
are monotone increasing in R) gives R10. QED.
Dependencies: C6-A (b), P0, L1. Control: 872: Rcap = 26,
Fp + S5 = 4 + 25 = 29 <= 104, S5 = 25 <= 52. 873s: Rcap = 1 + 5 + 0 + 0 + 0
= 6, Fp + S5 = 24 + 0 <= 24 (equality!), S5 = 0. Pass.

## R11: PEN = max(max(0,SH+ST-Sp), Ncyc-zp2g) <= NCh — verdict (a) PROVED
From E3-n6, LEMMAC-n6 and Ns <= NCh. E3 (reproduced): the pshits ps-started
short paths and the cnl CNL-emitting short paths are two families of distinct
short paths inside the Sp short paths, so at least pshits + cnl - Sp paths are
BOTH; such a path heads its chain (E1 argument: not hop-entered) and ends it
(E2: no hop leaves it), so its chain is a singleton short chain:
Ns >= max(0, SH + ST - Sp) with SH = pshits, ST = cnl. LEMMAC (reproduced):
edges with nc-run tails are exactly premature-sig edges, and such an edge has
an nc head iff it is a zp2g unit, so cycles without crit-runs use only zp2g
edges and, being edge-disjoint, number at most zp2g. A cycle K with a crit-run
contains the full crit-chain of that crit's link-path pi and an nc-run (the
edge leaving the chain end is a CNL with nc head), so pi has length <= 4 (P4:
<= 5 vertices, one an nc-run) — SHORT; the in-edge of crit-run(v_1) inside K
is not a link (crit-chains complete) nor a CNL (nc heads), so it is a ps-hit —
pi heads its chain; the out-edge of crit-run(v_l) has source y_{v_l}, a
completion d=2 exit landing on a non-crit — a CNL — so pi ends its chain: pi
is a singleton short chain, distinct for distinct (vertex-disjoint) cycles.
Hence Ns >= Ncyc - zp2g. Both give Ns >= PEN, and Ns <= NCh since singleton
chains are chains. QED.
Dependencies: E1, E2, P0, P4, L1. Control: 872: PEN = max(max(0,50-25),25-0)
= 25 <= 26 = NCh. 873s: PEN = 0 <= 6. Pass.

## R12: P - 2D <= 4*NCh - 2(SH+ST) - PEN — verdict (a)+(b)
LEMMAA-n6 (proof6.md §8) on top of FINITE CHECK C6-B (typed value caps).
C6-B (finite check, (b)): for every hop-chain, value := blocks - 2*cost obeys
value <= 4 - 2a - 2b - s (a/b = short-first/short-last flags, s = 1 iff the
chain is a single short path). Range and sufficiency: same abstract-chain
domain as C6-A — every chain occurring in any ordering is an abstract chain,
and the search is complete over that superset. Completeness of the pruned DFS
is itself a proved claim: the pruning bound value + (4 - runlen) + floor(RC/23)
is a valid upper bound on any extension because (i) the rest of the current
{4,5}-run adds at most 4 - runlen paths of value <= +1 each (C6-A), and (ii)
every later group (breaks of length <= 3 then a {4,5}-run) contributes value
<= 4 - 3 = +1 while consuming >= 3 + 4*5 = 23 classes, and only RC classes
remain. Certified by chain6.c and independently by chains871.c (typed caps
4/2/2/0/-1 agree).
LEMMAA (proved): link-paths partition into the NCh chains (P3: hop relation
acyclic), so P# = sum blocks and D = sum cost, whence
P# - 2D = sum_c value(c) <= sum_c (4 - 2a_c - 2b_c - s_c)
= 4*NCh - 2*SH* - 2*ST* - Ns <= 4*NCh - 2*SH - 2*ST - PEN,
the last step because SH* >= SH = pshits (E1), ST* >= ST = cnl (E2),
Ns >= PEN (E3 + LEMMAC), and all three appear with negative sign. QED.
Dependencies: C6-B (b), E1-E3, LEMMAC, P3. Control: 872:
P - 2D = 29 - 50 = -21; RHS = 104 - 100 - 25 = -21 — equality. 873s:
P - 2D = 24; RHS = 24 - 0 - 0 = 24 — equality. Pass.

## R13: P <= F_s and P <= F_C (Pareto frontiers) — verdict (a)+(b)
Structure: two FINITE CHECKS (the tables) + three PROVED reductions.
(b1) C6-C (chain Pareto table): for every cost c <= 16 (re-certified to 20 by
chains871.c) and endpoint type (a,b), g(c,a,b) is the max #link-paths in a
hop-chain of that cost and type. Range: all abstract chains of cost <= CMAX.
Sufficiency (why no ordering escapes): every hop-chain occurring in ANY
ordering is an abstract chain (class-disjoint L1-segments joined by d=3 hops
— all proved necessary properties, P0(b,e), L1, and hop acyclicity P3), so
the enumeration domain is a superset of the realizable chains; the WLOG head
123456 is licensed because alphabet relabelling is a letterwise bijection
commuting with rot, rho, sig, d, transitive on the 720 permutations, and
preserving cost, path lengths and endpoint types. For costs ABOVE the table
range the scanner does not extrapolate the table: cap() (scan871.py:379)
falls back to blocks <= 4 - 2a - 2b + 2c, which is C6-B rearranged
(value = blocks - 2*cost <= 4 - 2a - 2b) and holds for EVERY cost — so the
finite range needs no habitat bound; the sufficiency argument is complete.
The pruned-DFS completeness argument for the table search is proved in
proof6.md §7 (bound "remaining blocks <= (4 - runlen) + 5*floor(budget/2)":
any later {4,5}-run needs a cost >= 2 break before it and adds <= 4 paths).
Independent reimplementation: chain6.c vs chains871.c, entry-for-entry match.
(b2) C6-S (refined table): gS(c,s5,s4,a,b) for c <= 16, exhausted by
chains871 mode S; combinations absent are unrealizable (the enumeration is
exhaustive over the abstract superset). Beyond c = 16 the scanner uses
min(cap(c,a,b), _maxblocks(c,s5,s4,a,b)) (build_chaintypes, scan871.py:469),
both proved for all c — the second is CHAINRUN-n6, proved below. So again no
range gap.
(a1) CHAINRUN-n6 (proved, proof871.md §4, reproduced): in one chain let r =
#maximal {4,5}-runs of link-paths, a3/b3 = 1 iff the first/last path has
length <= 3. Distinct maximal runs are separated by at least one length-<=3
path (r - 1 separators), and a leading/trailing short-<=3 path is not a
separator, so s4 >= (r-1) + a3 + b3. A maximal {4,5}-run is a contiguous
subsequence of a chain, hence itself a chain of {4,5}-paths, so C6-A caps it
at 4 paths, at most 2 of length 4: blocks <= s4 + 4r, s5 <= 2r; r = 0 forces
s5 = 0, blocks = s4. Cost = s5 + sum over s4 paths of (5-l) gives
s5 + 2 s4 <= c <= s5 + 4 s4; and a = b = 1 with s5 + s4 = 1 forces
blocks = 1. QED.
(a2) PARETO-n6 (proved, proof6.md §8, reproduced): link-paths partition into
the NCh chains (hop acyclicity, P3), so P = sum blocks, D = sum cost; each
chain's blocks <= cap(cost, a, b) — the running maximum over costs <= c only
weakens; at least SH chains have a = 1 (E1) and ST have b = 1 (E2). F is the
EXACT maximum of this separable objective over NCh chains of total cost D
with the two obligation counts — a finite DP, so P <= F(NCh, D, SH, ST) for
every ordering.
(a3) PARETOS-n6 (proved, proof6.md §8 + proof871.md §3, reproduced): at least
Ns chains are single short paths; each has blocks = 1, cost = 5 - l in 1..4
(1 <= l <= 4 by L1 and shortness), endpoint type a = b = 1, so it discharges
one a- and one b-obligation. For any ns <= Ns, deleting ns of them leaves
NCh - ns chains carrying P - ns paths and cost <= D - ns, with obligations
max(0, SH - ns), max(0, ST - ns); F is monotone in the cost budget (machine-
checked over the used range by the gate), so
P <= ns + F(NCh - ns, D - ns, max(0,SH-ns), max(0,ST-ns)) =: F_s. The scanner
uses ns = PEN <= Ns (E3 + LEMMAC, see R11). F_C is the same partition
argument with each chain charged its exact (c, s5, s4, a, b) profile, blocks
capped by min(g running-max, gS or CHAINRUN, C6-B fallback), and the global
sums P, D, S5, S4 enforced exactly — every ingredient proved or certified
above, and the DP is again an exact maximum of a separable objective. QED.
Dependencies: C6-A/B/C/S (finite, (b)), CHAINRUN, PARETO, PARETOS, E1-E3,
LEMMAC, L1, P0, P3. Control (machine, logs/itemB_controls.log): 872:
Fs(26,25,25,25,25) >= 29 = P (proof6.md §8 records equality 25 + F(1,0,0,0)
= 29) and FCs passes; 873s: Fs(6,0,0,0,0) = 6*g(0,0,0) = 24 = P, equality.
All 97 objects PASS.

## R14: component packing — verdict (a) PROVED
From GROUPS-n6 (proof871.md §5), reproduced in full.
Setup: pointer graph on the 120 + e runs; edges = links, CNLs, premature-sig
exits (one per d=2 transition, S-exits excluded); in/out-degrees <= 1 and no
loops (rho has no fixed point on permutations with distinct letters), so
components are directed paths or cycles, each of <= 5 vertices (P4).
(i) Ncomp = P - cnl + Q2 + zp3 + Ncyc: V = 120 + e (P0(c));
E = #links + #CNL + #premature-sig = (120 - P) + cnl + (e - Q2 - zp3)
(P0(h): a class is link-entered iff not a path head; P2's split of the e
premature ends). V - E = P - cnl + Q2 + zp3 = #path components; add Ncyc.
(ii) each component g with m_g link-paths' crit-chains and k_g nc-runs
satisfies sum_j l_{g,j} + k_g = #vertices(g) <= 5: links are pointer edges,
so a path's whole crit-chain lies in one component; crit-runs and nc-runs
partition the runs (P0(c)).
(iii) k_g >= m_g - 1, and >= m_g if g is a cycle: the head crit-run of a path
in g has an in-edge inside g only of ps-hit type (not a link — the head would
not be a head; not a CNL — CNLs land on non-crits; S-exits give no edge), and
a ps-hit's TAIL is the run starting at rot(z) for premature z, which is an
nc-run (L12 argument: rot(z) = rot(y_{C(z)}) would force z = y_{C(z)},
contradicting premature). Distinct heads consume distinct nc-run tails
(out-degree <= 1). In a cycle every vertex has an in-edge (all m_g heads do);
in a path component exactly one vertex lacks one (at least m_g - 1 do).
(iv) sum m_g = P, sum k_g = e, sum of all lengths = 120 (every link-path in
exactly one component, every nc-run in exactly one, 120 classes).
(v) a component with m_g = 0 has only nc-runs, so all its internal edges have
nc tails AND nc heads: not links (crit heads), not CNLs (crit-run tails), so
premature-sig-to-noncrit = zp2g units; edge-disjointness bounds the total
edges of such components by zp2g, and each such PATH component's source
vertex is entered by a non-edge-generating or non-crit-landing event counted
by zq + zh + zp2s, distinct across components.
Hence the multiset of the P link-path lengths must pack into Ncomp groups
obeying (ii)-(v) — exactly the scanner's groups_feasible test, whose group-
type enumeration is complete because m_g >= 1 in a group needs
sum l >= m_g and k_g >= m_g - 1, so 2 m_g - 1 <= 5, m_g <= 3. QED.
Dependencies: P0, P1, P2, P4, L1, and the L12 tail argument; ACYCLIC (see DAG
below). Control: 872: Ncomp = 29 - 25 + 0 + 0 + 25 = 29 groups: 25 cycles
(l = 4 path + 1 nc-run = 5 vertices, k = 1 >= m = 1), 4 paths (l = 5, k = 0
>= m - 1 = 0); sum k = 25 = e. 873s: 24 path groups (l = 5, k = 0), sum k =
0 = e. Machine PASS on all 97.

## Dependency DAG (audit item: acyclicity and groundedness)
Level 0 (raw definitions only): P0 (Prop 1 a-h), T0-n6 + gap dichotomy,
DEFSPLIT, L1, L1a, L2(P4).  All proved directly from words/counting.
Level 1: T1(P1), T2(P2), PNUM/UNIT/THMM (use P0, L1, L1a).
Level 2: LEMMAS (T0 + dichotomy); E1 (P0, P4); E2 (P0, P4); E3 (E1, E2);
LEMMAC (P0, P4, L1); L12 (P0 + LEMMAC's Step-1 edge classification — NOT
LEMMAC's conclusion, no cycle); T7 (P0, P1, P2, L1a); LU8 (P0, P1, P4).
Level 3 (finite checks over the abstract-chain superset defined by L1 +
P0(b,e) + hop-acyclicity): C6-A, C6-B, C6-C, C6-S — each certified by two
independent implementations (chain6.c, chains871.c), no lemma inputs beyond
the superset definition.
Level 4: LEMMAR (C6-A, P0); CHAINRUN (C6-A); LEMMAA (C6-B, E1-E3, LEMMAC);
PARETO (C6-C, E1, E2, P3); PARETOS (PARETO, E3, LEMMAC, L1); GROUPS (P0-P2,
P4, L1, L12-argument).
Checked pairwise: no rule's derivation cites any result derived from that
rule.  The one flagged risk — L12 citing "LEMMAC Step 1" while LEMMAC is
listed after it — is benign: LEMMAC's own proof of Step 1 (cycle edges with
nc tails and nc heads are zp2g units) uses only the edge typing of P0 and
never L12.  The DAG is acyclic and grounded in the raw definitions.

## Scanner substitutions audited for direction-soundness
(1) SH := hits, ST := cnl (true SH*, ST* >= these, E1/E2): all uses monotone-
safe (R9 weaker, R11 PEN smaller, R12 RHS larger, R13 obligations weaker).
(2) X4h := X4 (true X4h <= X4): X4h appears only positively in the caps of
R9 and R10, so the substitution is the WEAKEST instance — sound.
(3) R4 uses floor(slack/4) >= floor(interior slack/4) — weakening of the
proved LEMMAS — sound.
(4) cap() running maximum over costs <= c — monotone weakening — sound.
Each weakening admits every profile the true constraint admits, so no real
ordering is rejected; the finite-check tables are used only within their
certified ranges with proved-for-all-c fallbacks beyond.
