# Item A — Complete proofs of Lemma 3.4's six inequalities (n = 6)

Auditor: T-n6-audit. Source formalism: `approaches/bounds/bounds.md`
(the "companion formalism" the paper cites); all proofs below are reproduced
from it in self-contained form, specialized to n = 6, in dependency order,
and control-checked (`checks/itemA_control_check.py`, log
`logs/itemA_control_check.log`) against the verified 872 and the 96
verified 873s. Variable dictionary (paper Lemma 3.4 -> this file):

| paper | here | meaning |
|-------|------|---------|
| x     | extra | m - 120 = sum_C (k_C - 1) |
| x3    | e3    | sum_{k_C>=3} (k_C - 1) |
| d2    | d2    | #{C : k_C = 2} = x - x3 |
| f     | F     | # non-full runs = extra + dirty |
| q     | Q2    | # S-type (re-entry) transitions |
| c     | Ncyc  | # pointer-graph cycles |
| a     | alpha | # transitions of weight >= 3 |
| y     | h     | sum over transitions of max(w-3, 0) = X4 |
| m     | m     | # runs = 120 + extra |
| Delta | Delta | 5(1 + alpha + Q2 + Ncyc) - m |
| PT    | PT    | # pure tours |

## 0. Setup (raw definitions)

Work with the 720 permutations of [6]. For permutations p, q let
ov(p,q) = the largest k such that the last k letters of p equal the first
k letters of q, and d(p,q) = 6 - ov(p,q). Maps: sigma(p) = p2..p6 p1
(left rotation), tau(p) = p3..p6 p2 p1, rho(p) = p2 p3 p4 p5 p1 p6.
C(p) = {sigma^k(p)} is the rotation class (1-cycle) of p; there are 120
classes of 6 elements each.

A *first-occurrence ordering* (equivalently, Hamiltonian sequence) is a
listing P = (q_1, ..., q_720) of all 720 permutations, each once. Its
weights are w_i = d(q_i, q_{i+1}), i = 1..719. (By the reduction lemma —
bounds.md Lemma 4 — every superpermutation of length L induces such an
ordering with 6 + sum w_i <= L; this is the only bridge to L(6) and is
not under audit here.) Throughout, "targets are unvisited": every vertex
of P occurs exactly once.

Fix P. *Runs* are the maximal segments of consecutive vertices joined by
weight-1 steps. Facts P1-P4 below are elementary; proofs as in bounds.md
Lemmas 1-3, 5, 8, reproduced:

**P1.** d(p,q) = 1 iff q = sigma(p); sigma^k(p) = p iff 6 | k.
*Proof.* ov = 5 forces q_1..q_5 = p_2..p_6 and q_6 = the missing letter
= p_1, so q = sigma(p); conversely ov(p, sigma p) = 5 exactly (sigma(p)
!= p since the letters are distinct). sigma^k(p) has first letter
p_{(k mod 6)+1}, equal to p_1 iff 6 | k, and sigma^6 = id. QED

**P2.** d(p,q) = 2 iff q in {sigma^2(p), tau(p)}; these are distinct,
sigma^2(p) in C(p), tau(p) not in C(p).
*Proof.* ov = 4 means q = p_3 p_4 p_5 p_6 x y with {x,y} = {p_1, p_2};
the two orders give sigma^2(p) and tau(p). They differ in the last
letter. tau(p)'s cyclic word transposes the cyclically adjacent letters
p_1 p_2, changing the cyclic word, so tau(p) is in no rotation of p. QED

**P3.** rho^k(p) = p iff 5 | k; the classes C(p), C(rho p), ...,
C(rho^4 p) are pairwise distinct; and tau = rho o sigma.
*Proof.* rho fixes p_6 and rotates p_1..p_5, so P1's argument on 5
letters gives the order. For distinctness: rho^k(p) (0 <= k <= 4) as a
cyclic word is the cyclic 5-word (p_1..p_5) with p_6 inserted after p_k
(p_0 := p_5); equal insertions force equal insertion points. Composition:
rho(sigma(p)) = rho(p_2..p_6 p_1) = p_3 p_4 p_5 p_6 p_2 p_1 = tau(p). QED

**P4 (runs).** By P1, a run is a sigma-arc {b, sigma(b), ...,
sigma^{l-1}(b)} inside a single class, of length l <= 6; it is *full* if
l = 6. Let m = # runs; each class C is partitioned by the runs it
contains into k_C >= 1 arcs; C is *dirty* if k_C >= 2, and all k_C >= 2
arcs of a dirty class are non-full. Set extra = m - 120 =
sum_C (k_C - 1), e3 = sum_{k_C >= 3} (k_C - 1), d2 = #{C : k_C = 2}
(= extra - e3), dirty = #{C : k_C >= 2}, F = # non-full runs =
sum_{C dirty} k_C = extra + dirty. The m - 1 steps between consecutive
runs (*transitions*) all have weight >= 2 (weight 1 would contradict run
maximality, P1). alpha = # transitions of weight >= 3, and
h = sum over transitions of max(w - 3, 0). Total cost identity:
sum_i w_i = (720 - m)·1 + sum over transitions of w
= 720 + m - 2 + alpha + h' where h' counts (w-2)-excess... precisely:
sum w_i = (720 - m) + 2(m-1) + (alpha + h) = 838 + (extra + alpha + h),
since each transition contributes 2 + [w>=3] + max(w-3,0). So with
t := extra + alpha + h, cost = 838 + t and W = 119 + t in the paper's
normalization. (Identity machine-verified on all 97 controls.)

**P5 (O1/O2).** (O1) Every transition target is a run start. (O2) For a
run-end e, sigma(e) is a run start: if e's run is full, sigma(e) is its
own start; else the runs in C(e) form k >= 2 arcs, e ends one, and
sigma(e) begins the cyclically next arc.

**P6 (transition typing).** By P2 each weight-2 transition from run-end
e goes to tau(e) (*T-type*, count P2#) or sigma^2(e) (*S-type*, count
Q2); weight >= 3 is *J-type* (count alpha). P2# + Q2 + alpha = m - 1.

## 1. The pointer graph; inequality (iii)

**Definition.** Vertices: the m runs. For each T-type transition with
source end e and target tau(e), draw the edge r -> r' where r = the run
starting at sigma(e) (a run start by O2) and r' = the run starting at
tau(e) (a run start by O1). Since tau(e) = rho(sigma(e)) (P3), every
edge satisfies start(r') = rho(start(r)). The edge r -> r' exists iff
the entry transition of r' is T-type. (Caution: the transition's source
run — the path-predecessor of r' — need not be r.)

**Lemma A1 (= bounds.md Lemma 9).** Every run has in-degree <= 1 and
out-degree <= 1 in the pointer graph; components are directed chains and
directed cycles; every component has at most 5 runs; and
#chains = m - P2# = 1 + Q2 + alpha.

*Proof.* In-degree: an in-edge of r' corresponds to the entry transition
of r', which is unique. Out-degree: an out-edge of r corresponds to a
transition arriving at the single vertex rho(start(r)), and at most one
step of P arrives at any vertex. Distinct T-transitions have distinct
targets, hence distinct edges, so #edges = P2#. A digraph with all
degrees <= 1 splits into chains and cycles, and #chains = #vertices -
#edges = m - P2# = 1 + Q2 + alpha (P6). Sizes: along an edge, starts
advance by rho, so a component with t runs has starts b, rho(b), ...,
rho^{t-1}(b); if t >= 6 then runs 1 and 6 are distinct runs with the
same start rho^5(b) = b (P3) — impossible, since a start determines its
run. QED

**Inequality (iii): Delta := 5(1 + alpha + Q2 + Ncyc) - m >= 0.**
(Ncyc = # cycle components.)

*Proof.* The m runs are partitioned into (1 + Q2 + alpha) chains and
Ncyc cycles (Lemma A1), each of size <= 5. So
m <= 5(1 + alpha + Q2 + Ncyc). QED   [= bounds.md (C6)]

**Lemma A2 (cycle components are full 5-cycles).** Every pointer cycle
has exactly 5 runs. *Proof.* A cycle of size t has rho^t(b) = b, so 5 | t
(P3); and t <= 5 (Lemma A1); so t = 5. QED
Consequently Delta = sum over CHAIN components of (5 - size): cycles
contribute 0. In particular #short chains (size < 5) <= Delta.  (*)

## 2. S-transitions and launchers; inequalities (i) and (ii)

**Lemma A3 (= bounds.md Lemma 10).** Let an S-type transition leave run
q (an arc of class C) at end e, with target sigma^2(e). Then:
1. q is not full — if it were, sigma^2(e) = sigma(sigma(e)) =
   sigma(start(q)), a vertex already visited inside q. Hence C is dirty.
2. The arc of C following q is the singleton {sigma(e)}, and the target
   sigma^2(e) starts the arc after that: sigma(e) is a run start (O2)
   and sigma^2(e) is a run start (O1); were the arc at sigma(e) of
   length >= 2, sigma^2(e) would be interior to it, not a start.
3. That target arc is entered exactly one time-step after q exits.
4. C receives exactly k_C entries (one per arc). The first-visited
   vertex of C is the global path start or the target of a transition
   whose source lies OUTSIDE C; either way the entry into the
   first-visited arc of C is not an S-transition-from-C. S-transitions
   from C are entries into C from C, so #(S-transitions with source in
   C) <= k_C - 1.

**Lemma A4 (= bounds.md Lemma 11, launchers).** Let K be a pointer
cycle, s* its earliest-entered run, q_K the run whose exit transition is
the entry of s* (s* has an in-edge, so it is not the first run of P).
Then: (1) the exit of q_K is T-type; (2) q_K is not in K — else
entry(q_K) >= entry(s*) = exit(q_K) + 1 > entry(q_K); (3) q_K is not
full: the in-neighbor r of s* is the run starting at sigma(end(q_K)),
and r in K (in a cycle, every member's in-neighbor is a member); if q_K
were full then r = run(sigma(end(q_K))) = run(start(q_K)) = q_K in K,
contradicting (2); hence q_K is a non-full arc of a dirty class; (4) the
arc following q_K's arc in its class is the run r in K (by O2,
sigma(end(q_K)) starts the cyclically next arc, and that arc is r);
(5) K -> q_K is injective (q_K's exit is one transition and enters the
earliest run of exactly one component).

**Inequality (i): Q2 + Ncyc <= extra.**  [= bounds.md Lemma 12]

*Proof.* Charge each pointer cycle K to the arc q_K (Lemma A4) and each
S-transition to its source arc. All charged arcs are non-full arcs of
dirty classes (A3(1), A4(3)). Each arc carries at most one charge: an
arc has at most one exit transition; if that exit is T-type the arc can
only be a launcher, of at most one cycle by A4(5); if S-type, only an
S-source; distinct S-transitions have distinct source runs. Since
extra = sum_{C dirty} (k_C - 1), it suffices to show every dirty class
has at least one uncharged arc.

Suppose all k = k_C >= 2 arcs A_1, ..., A_k of a dirty class C (in
cyclic sigma-order, indices mod k) are charged; write t_i <= x_i for the
entry/exit times of A_i. Claim: for every i there is j(i) in {i+1, i+2}
with t_{j(i)} > t_i.
- A_i a launcher of cycle K: by A4(4) the following arc A_{i+1} is a run
  of K, so t_{i+1} >= entry(s*_K) = x_i + 1 > t_i; take j(i) = i+1.
- A_i an S-source: by A3(2,3), A_{i+1} = {sigma(end(A_i))} is a
  singleton and the target is start(A_{i+2}), entered at time x_i + 1.
  If A_{i+2} = A_i (k = 2), the target start(A_i) was visited at
  t_i <= x_i — but targets are unvisited: absurd. Otherwise
  t_{i+2} = x_i + 1 > t_i; take j(i) = i+2.
Iterating i -> j(i) yields arcs of strictly increasing entry time within
a finite set — some index repeats, contradiction. Hence some arc of C is
uncharged, and #charges = Q2 + Ncyc <= sum_{C dirty}(k_C - 1) = extra. QED

**Inequality (ii): Q2 <= e3.**  [= bounds.md Lemma 16]

*Proof.* Let an S-transition have source arc q in class C. If k_C = 2:
by A3(2) the arc after q is the singleton {sigma(e)} and the target
starts the arc after THAT — which is q itself, so the target is
start(q), visited when q was entered — contradicting that targets are
unvisited. Hence k_C >= 3 for every S-source class. By A3(4) each class
hosts at most k_C - 1 S-transitions, so
Q2 <= sum_{k_C >= 3} (k_C - 1) = e3. QED

## 3. Pure tours; inequalities (iv) and (v)

**Definition.** A pointer chain is *pure* if all its runs are full, and
a *pure tour* if moreover it has exactly 5 runs. PT = # pure tours.

**Inequality (iv): PT >= 1 + alpha + Q2 - Delta - (F - Ncyc).**
[= bounds.md Lemma 17]

*Proof.* There are exactly 1 + alpha + Q2 chains (Lemma A1). A chain
fails to be a pure tour only by being short (< 5 runs) or impure
(containing a non-full run). By (*) after Lemma A2,
#short chains <= Delta. Every pointer cycle K contains a non-full run:
by A4(3,4) the arc following the launcher q_K is a run r in K lying in
q_K's dirty class, hence non-full; distinct cycles contain distinct such
runs (components are disjoint). So at least Ncyc of the F non-full runs
lie in cycles, and at most F - Ncyc of them lie in chains; hence
#impure chains <= F - Ncyc. Therefore
PT >= #chains - #short - #impure >= (1 + alpha + Q2) - Delta - (F - Ncyc). QED

**Inequality (v): PT <= floor(m / 5).**

*Proof.* Pure tours are pairwise disjoint components of 5 runs each, out
of m runs in total: 5·PT <= m. QED
[Asserted in bounds.md's Theorem-5 constraint list, "0 <= PT <=
floor(m/(n-1))"; the proof is the one line above.]

## 4. Segments and stretches; inequality (vi)

Two computational facts about weight-3 steps, from bounds.md Lemmas 14
and 15 (their general parts only — no equality-case hypothesis is used):

**Lemma A5 (weight-3 targets).** For a permutation e: d(e,q) = 3 iff
q = e_4 e_5 e_6 y_1 y_2 y_3 with (y_1,y_2,y_3) an arrangement of
{e_1,e_2,e_3}. Say a class family ("2-loop") with distinguished letter
delta and base w (a cyclic word on the other 5 letters) is the set of
classes {C : cyclic(C) - delta = w}; each class belongs to exactly one
2-loop per letter, and the 5 classes C(b), C(rho b), ..., C(rho^4 b) are
precisely the 2-loop of b with delta = b_6 (P3). Let T be the 2-loop of
sigma(e) (delta = e_1, base cyclic(e_2..e_6)) and let q be a weight-3
target of e. Then:
1. the identity arrangement gives q = sigma^3(e) in C(e);
2. for the four arrangements other than identity and reversal
   (e_3,e_2,e_1), the 2-loop of q (delta = y_3, base
   cyclic(e_4 e_5 e_6 y_1 y_2)) INTERSECTS T;
3. for the reversal q* = e_4 e_5 e_6 e_3 e_2 e_1, the 2-loop of q* is
   DISJOINT from T.
*Proof.* Overlap 3 means exactly q = e_4 e_5 e_6 (perm of e_1 e_2 e_3);
no larger overlap is possible since q starts with e_4. (1) Clear.
(2) Case y_3 = e_1, (y_1,y_2) = (e_2,e_3): base' = cyclic(e_4 e_5 e_6
e_2 e_3) = base, T' = T. Case y_3 = e_2: v = cyclic(e_4 e_5 e_6 e_2 e_1
e_3) resp. cyclic(e_4 e_5 e_6 e_2 e_3 e_1) (for (y_1,y_2) = (e_1,e_3)
resp. (e_3,e_1)): deleting e_2 gives base', deleting e_1 gives base; so
the class v lies in T' and in T. Case y_3 = e_3, (y_1,y_2) = (e_2,e_1):
v = cyclic(e_4 e_5 e_6 e_2 e_3 e_1): delete e_3 -> base', delete e_1 ->
base. (3) T' has delta = e_1, base' = cyclic(e_4 e_5 e_6 e_3 e_2); a
common class would force base = base', but in base the successor of e_3
is e_4 and in base' it is e_2. QED
(Machine checks F8, F10, F11 in bounds/checks/level3_check.py, exhaustive
for n = 4..7, PASS.)

**Lemma A6 (the E map).** E(e) := sigma^{-1}(rho^4(q*)) =
(e_1, e_2, e_4, e_5, e_6, e_3). E fixes e_1, e_2 and 4-cycles
(e_3,e_4,e_5,e_6); hence E^4 = id and E^k(e) != e for 0 < k < 4.
*Proof.* Direct computation: rho^4 = rho^{-1} maps p to
(p_5, p_1, p_2, p_3, p_4, p_6); applied to q* = (e_4,e_5,e_6,e_3,e_2,e_1)
it gives x = (e_2, e_4, e_5, e_6, e_3, e_1), and sigma^{-1}(x) =
(x_6, x_1..x_5) = (e_1, e_2, e_4, e_5, e_6, e_3). Order: P1 on the
rotation of (e_3,e_4,e_5,e_6). QED (machine check F9.)

**Lemma A7 (segments; = bounds.md Lemma 18).** Cut the path-ordered run
sequence before every run whose entry is the path start, a J-transition,
an S-transition, or a T-transition with non-full source run; the pieces
are *segments*. Let Ftau = #T-transitions with non-full source. Then:
1. #segments = 1 + alpha + Q2 + Ftau, and Ftau <= F - Q2;
2. inside a segment, each run is the pointer-successor of the previous;
3. every pure tour is exactly one segment, and the transition leaving
   its last run is J-type.
*Proof.* (1) Every transition is J, S, or T, and T splits by fullness of
its source run; #cuts = 1 + alpha + Q2 + Ftau = #segments. Each run has
at most one exit; S-sources are non-full (A3(1)) and pairwise distinct,
so the non-full runs with T-exits number at most F - Q2. (2) A non-cut
run r is entered by a T-transition from a full source run p; then
sigma(end(p)) = start(p), so the pointer edge of that transition is
p -> r, and p is the path-predecessor of r. (3) Let U be a pure tour.
Its head has no in-edge; since every T-type entry of a run r
creates an in-edge of r (the edge run(sigma(end(src))) -> r), the head's
entry is the path start, J-type, or S-type — in every case a cut. Interior runs r of U: r has an in-edge, so its entry is
T-type from some source run p. If p were non-full, the edge tail
r' = run(sigma(end(p))) is the arc following p's arc inside p's dirty
class (O2), hence non-full; but r' is the chain-predecessor of r, a
member of the pure tour U — contradiction. So p is full, the edge tail
is p itself, p is the chain-predecessor of r AND the path-predecessor of
r (the transition leaves p and enters r): interior entries are uncut and
path-contiguous, so U is one segment, traversed in chain order. Exit:
the transition leaving U's last run r5 (full) is not T-type — a T-exit
of a full run creates an out-edge of r5, impossible at a chain end — and
not S-type (S-sources are non-full, A3(1)); so it is J-type. QED

**Lemma A8 (stretches; = bounds.md Lemma 19).** A pure tour U, being a
5-run chain of full runs with starts b, rho(b), ..., rho^4(b), fully
traverses the 5 classes of the 2-loop of b (P3), path-contiguously
(A7(3)). Say pure tours A -> B are *linked* if B's first run immediately
follows A's last run in path order with a connecting transition of
weight exactly 3. Then:
1. if A -> B are linked with e = last vertex of A, then B starts at the
   reversal q* = e_4 e_5 e_6 e_3 e_2 e_1 and ends at E(e);
2. a maximal chain of linked tours (*stretch*) has at most 4 tours;
3. PT <= 4 (1 + h + (#segments - PT)).
*Proof.* (1) The connecting weight-3 target is one of A5's six. The
identity arrangement is sigma^3(e), inside A's last class — visited. For
the four middle arrangements, A5(2) gives a class in both B's 2-loop and
A's 2-loop (A's last run is full and lands T = the 2-loop containing
C(e)... precisely: A traverses the 2-loop of its first start b_A, and
C(e) = C(rho^4(b_A)) is a member; T as defined in A5 is the 2-loop of
sigma(e), which equals the 2-loop traversed by A, since sigma(e) =
start of e's run... e's run is full so sigma(e) = its start, one of
rho^k(b_A)); B traverses its own 2-loop fully; a shared class would have
its 6 vertices traversed by both A and B — revisits, impossible. So the
target is q*, B's first start is q*, and B's last vertex is
sigma^5(rho^4(q*)) = sigma^{-1}(rho^4(q*)) = E(e) (Lemma A6). (2) By
(1), k linked tours have last vertices e, E(e), ..., E^{k-1}(e); tours
are disjoint so these are distinct; E^4 = id (A6) forces k <= 4.
(3) #stretches >= PT/4 by (2). Between two consecutive stretches (path
order) there is either a weight >= 4 transition directly joining two
adjacent pure tours — each such contributes >= 1 to h, distinct
separations using distinct transitions — or at least one intervening
non-tour segment (pure tours are single segments by A7(3), so the
material between stretches is a union of complete segments, none a pure
tour; distinct separations use distinct segments). No weight-3
tour-to-tour separator exists: adjacent tours joined at weight 3 are
linked, i.e. same stretch; and by A7(3) the exit of a tour is J (w >= 3),
so w >= 4 is the only adjacent separator. Hence
#stretches <= 1 + h + (#segments - PT), and PT <= 4·#stretches. QED

**Inequality (vi): 5 PT <= 4 (2 + h + alpha + F).**

*Proof.* By A7(1), #segments = 1 + alpha + Q2 + Ftau <= 1 + alpha + Q2 +
(F - Q2) = 1 + alpha + F. Substituting into A8(3):
PT <= 4(1 + h + 1 + alpha + F - PT) = 4(2 + h + alpha + F) - 4 PT,
so 5 PT <= 4(2 + h + alpha + F). QED

## 5. The dirty-cap lemma and the integer scan (min t = 24)

**Lemma A9 (dirty cap).** dirty <= d2 + floor(e3 / 2).
*Proof.* dirty = #{k_C = 2} + #{k_C >= 3} = d2 + #{k_C >= 3}, and each
class with k_C >= 3 contributes k_C - 1 >= 2 to e3, so
#{k_C >= 3} <= floor(e3 / 2). QED

**Lemma A10 (monotone relaxation in F).** Among (i)-(vi), F appears only
(a) subtracted on the right of the LOWER bound (iv) for PT and (b) added
inside the UPPER bound (vi) for PT. Hence replacing the true value
F = extra + dirty by the maximal value F* = extra + d2 + floor(e3/2)
(>= F by Lemma A9) only enlarges the feasible PT-interval; every profile
realized by an ordering therefore satisfies the system AT F = F*, and a
minimum of t over the F*-system is a valid lower bound for all orderings.
QED

**Proposition A11 (base bound; FINITE-CHECK component).** Every
first-occurrence ordering of the 720 permutations has
t = extra + alpha + h >= 24; hence cost >= 838 + 24 = 862, W >= 143, and
L(6) >= 6 + 862 = 868.

*Proof.* By Sections 1-4, the integer vector (extra, e3, Q2, Ncyc,
alpha, h, PT) of any ordering satisfies: e3 <= extra, Q2 <= min(e3,
extra - Ncyc), Q2 + Ncyc <= extra (i,ii), Delta >= 0 (iii), (iv), (v),
(vi) at F = F* (Lemma A10), all variables >= 0.

*Range sufficiency.* Suppose t <= 23. Since extra, alpha, h >= 0 and
t = extra + alpha + h, each of extra, alpha, h is <= 23; then
e3 <= extra <= 23, Q2 <= e3, Ncyc <= extra - Q2, m = 120 + extra, and
PT is confined to [0, floor(m/5)]. So every ordering with t <= 23 lies
inside the finite box scanned below; exhaustive infeasibility of the box
proves t >= 24 for ALL orderings, with no residual unbounded case.

*The scan.* checks/itemA_scan6.py (this audit; independent
reimplementation from the constraint list alone) enumerates all
(extra, alpha, h) with extra + alpha + h <= 28 and all admissible
(e3, Q2, Ncyc), tests (iii) and the PT-interval
[max(0, 1 + alpha + Q2 - Delta - (F* - Ncyc)),
 min(floor(m/5), floor(4(2 + h + alpha + F*)/5))],
and reports min t = 24, attained at (extra, e3, Q2, Ncyc, alpha, h) =
(0, 0, 0, 0, 24, 0), Delta = 5, PT forced to 20 — exactly the paper's
stated tight profile. Log: logs/itemA_scan6.log. The project's original
scanner (bounds/checks/certify_scan.py; also certify_scan10/11.py with
additional constraints) independently reports n=6 min t = 24
(bounds/logs/certify_scan10.log, certify_scan11.log) — matching counts
from independent implementations. QED

*Calibration (from bounds.md Theorem 5):* the same system at n = 5
yields min t = 6, i.e. L(5) >= 153 = the true value, matching the two
tight profiles found by the exhaustive n = 5 search (bounds.md §5) —
evidence the system is not over-strong.

## 6. Control validation

checks/itemA_control_check.py (this audit) recomputes every profile
variable from the raw definitions (first-occurrence extraction, d by
overlap, runs, classes, pointer graph with edge rule
run(sigma(end)) -> run(tau(end)), component walk) for the verified 872
(approaches/n6/data/best872.txt) and all 96 verified 873s
(approaches/n6/data/block873/sol*.txt), asserts every structural claim
used above (runs are sigma-arcs; component sizes <= 5; cycle components
have size exactly 5; starts advance by rho along edges; #chains =
1 + Q2 + alpha; cost = 838 + t), and tests (i)-(vi) plus Lemma A9.
Result (logs/itemA_control_check.log): 97/97 sequences, 0 violations.
The controls exercise the system non-trivially:
- 872: (extra, e3, d2, F, Q2, Ncyc, alpha, h, Delta, PT) =
  (25, 0, 25, 50, 0, 25, 3, 0, 0, 3), t = 28 — Delta = 0 tight,
  25 pointer cycles (so (i) is tight: Q2 + Ncyc = 25 = extra);
- all 96 873s: (0, 0, 0, 0, 0, 0, 23, 6, 0, 24), t = 29 — Delta = 0 and
  (v) tight (PT = 24 = m/5), h = 6 exercising (vi): 5·24 = 120 <=
  4(2 + 6 + 23 + 0) = 124.

## 7. Dependency DAG (acyclicity)

P1, P2, P3 (elementary computations)
  -> P4 (runs), P5 (O1/O2), P6 (typing)      [+ Hamiltonicity only]
  -> A1 (pointer structure)                   -> (iii)
  -> A2 (cycles are 5-cycles)                 [P3, A1]
  -> A3 (S-transitions)                       [P2, P5]
  -> A4 (launchers)                           [A1, P5]
  -> (i)  Lemma 12 charge argument            [A3, A4]
  -> (ii) Lemma 16                            [A3]
  -> (iv) Lemma 17                            [A1, A2, A4]
  -> A5, A6 (weight-3 computations)           [P3 only]
  -> A7 (segments)                            [A3, P5, P6, A1]
  -> A8 (stretches)                           [A5, A6, A7, P3]
  -> (vi)                                     [A7, A8]
  -> (v)                                      [definition of PT]
  -> A9, A10 (scan soundness)                 [definitions, (iv), (vi)]
  -> A11 (min t = 24, FINITE-CHECK)           [(i)-(vi), A9, A10]
Every arrow points from earlier to later sections; no result cites a
later one; the roots are raw definitions plus "each permutation occurs
exactly once". In particular NONE of (i)-(vi) assumes any bound on cost,
length, or type — they are proved for EVERY ordering, so their use
inside a pruned search is sound. No circularity.
