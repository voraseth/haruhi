# cg.md — Lemma 6.8 (Closure topology): the intended object, a full re-proof,
# the downstream audit, and the controls

Workdir `approaches/n6cg`.  Target: `report/PAPER-n6-872.tex` Lemma~\ref{lem:closure}
(printed as Lemma 6.8), lines 1360–1468.

## 0. VERDICT, FIRST

**The repair holds.  The lemma is TRUE under the corrected vertex set, its
proof goes through unchanged apart from the one phrase, no downstream consumer
needs the printed (wrong) vertex set, and the two-loop bound is untouched.**
Nothing in the coverage argument is open at this point.

More precisely:

* The intended object is **CG has as vertices the hop-chains that do not lie in
  pointer *cycle* components** ("free chains").  This is *verbatim* the
  definition in the source artifact `approaches/n6coverage/coverage.md` §5.1
  and in the review record `reviews/R-n6-9.md` §1(a), and it is what
  `reviews/R-n6-7-workdir/mysweep.c` implements.  The paper's phrase "not
  forced singletons" is a transcription error: it imported the *different*
  quantity LAMBDA of TC4/§6.2.
* The printed definition is not merely off by a3 + b_q1 in the count — it makes
  the lemma's own **part (1) false**: at b_q1 = 1 it deletes q_1's chain, which
  part (1) names as the source of the linear path, and at a_3 >= 1 it deletes
  the middle chain of every three-block component, leaving arcs with no
  endpoint.  So the printed definition is self-inconsistent, and the count in
  the proof is the correct one, exactly as the coordinator's arithmetic shows.
* The two-loop bound (part (3)) is **independent of the vertex set**: it is an
  arithmetic bound on U = a_2 + 2 a_3, which is an *arc* count, derived from
  deficiency accounting + the identities + the run caps.  It survives verbatim.

## 1. WHAT THE CLOSURE GRAPH ACTUALLY RANGES OVER

### 1.1 The source artifacts

`approaches/n6coverage/coverage.md` §5.1, Definition (the document the paper's
§6.2 was written from):

> A chain is a maximal sequence of link-paths joined by hops (TC1).  By TC3.3
> every cycle link-path is a singleton chain; call those *cycle chains*, and
> call the others *free chains* (their link-paths all lie in path components).
> The *closure graph* CG has the free chains as vertices …

`reviews/R-n6-9.md` §1(a):

> **(a) The closure graph is a functional graph.**  Exclude the cycle singleton
> chains … The remaining chains at a Z = 0 census with a3 = c2 = 0 … number
> a2 + 1 + X4h.

(a_2 + 1 + X4h is a_2 + 2a_3 + 1 + X4h at a_3 = 0.)  R-n6-9 §1(c) is explicit
that q_1's chain **is** a vertex even when b_q1 = 1:

> If bq1 = 1, q1's own M2's edge leaves q1's chain, which has in-degree 0 and
> therefore lies on the linear path — that edge is never in a loop.

### 1.2 The executed code

`reviews/R-n6-7-workdir/mysweep.c`:

* l.196 / l.288 `if(m2n > (in_loop ? 0 : bq1))` — outside a loop b_q1 spans are
  reserved; **q_1's chain carries a span arc on the linear part**, i.e. it is a
  CG vertex whose out-arc is a span arc.  Under the printed definition that
  vertex would not exist.
* l.348 `if(loops_left > 0 && (m2n > bq1 || bn))` — the second-loop budget is
  `a_2 − b_q1 + bn`, i.e. the span arcs *other than q_1's* plus the defect arc.
  The engine budgets **arcs**, never vertices.
* The engine has no three-block piece at all (licensed by Lemma
  \ref{lem:c2z}: a_3 = 0 in every emitted configuration), so the a_3 middle
  chains never arise in the searched instances; the discrepancy is invisible to
  the search and is purely a defect of the printed statement.

`report/PAPER-n6-872.tex` l.2489 says the same thing in prose: "if $b_{q_1}$ is
set, $q_1$'s chain must first close a span".

### 1.3 Precise statement of the intended object

> **Definition (free chain, CG).**  Let SIGMA be a first-occurrence ordering
> with Z = 0 and slack = 0.  A *hop-chain* is a maximal sequence of link-paths
> joined by hops (TC1); there are NCh = e + 1 + X4h of them.  Call a hop-chain
> a *cycle chain* if its link-paths lie in pointer **cycle** components and a
> *free chain* otherwise.  (By TC3.3 every cycle link-path is a singleton
> chain, so the two classes partition the chains and no chain is mixed.)
>
> `CG` is the digraph on the **free chains**, with an arc A -> B whenever the
> transition that ends A triggers the head of B: either A's ender emits the CNL
> into a non-critical run of a *path* component whose ps-hit enters B's head
> ("span arc"), or A's ender emits a cost->=4 heavy landing on B's head crit
> ("d4 arc"), or (defect class only) A's ender performs the zh/zp3 defect join
> into B's head ("defect arc").

The three arc kinds are exactly the three the paper already lists.  **Only the
vertex set changes.**

## 2. LEMMA 6.8, RE-PROVED IN FULL

Raw inputs: F1–F4, P0–P4 (`approaches/n6audit/itemB_proofs.md` §Preliminaries),
TC1, TC1-end, TC1z, TC2, TC2c, TC3, TC4 (`approaches/n6tight/proof_tight.md`
§3–§5), Lemma K2 (defect class), the identities (I-a)–(I-d).  No census output,
no ledger, no search log.

### 2.1 The chains partition into cycle chains and free chains

Every link-path lies in exactly one pointer component (TC2).  By TC3.3 every
link-path of a *cycle* component is both ps-entered and CNL-emitting, hence
both heads and ends its chain: it is a singleton chain.  Therefore a chain
containing one cycle link-path contains nothing else, and every chain is either
a cycle chain (one cycle link-path) or a free chain (all its link-paths lie in
path components).  The number of cycle chains is the number of cycle
link-paths, c_1 + 2c_2.  Hence, by TC1 and (I-b),

    |V(CG)| = NCh − (c_1 + 2c_2) = (e + 1 + X4h) − (c_1 + 2c_2)
            = a_2 + 2a_3 + 1 + X4h .                                    (V)

This is the count used in the printed proof.  (`checks/symbolic.py` confirms
(V) and confirms that the printed definition instead yields
LAMBDA = a_2 + a_3 + 1 + X4h − b_q1, the TC4 quantity, differing by a_3 + b_q1.)

### 2.2 The arc inventory is exact

By TC1-end the NCh chain heads are exactly: q_1's path (entered by nothing, F3),
the e ps-hit-entered path heads, and the X4h paths entered by a cost->=4 heavy;
dually the NCh enders are exactly: the e CNL-emitting paths, the global-end
path, and the X4h paths whose end emits a cost->=4 heavy.

Each of the e non-critical runs receives exactly one CNL (TC2(a)) and generates
exactly one ps-hit (TC2(b)), so the e non-critical runs biject with the
(CNL-ender, ps-head) pairs — one candidate arc each.  By (I-b), c_1 + 2c_2 of
those runs lie in cycle components; for those, TC2 alternation puts both the
emitting and the entered link-path *in that same cycle*, so both are cycle
chains and the arc is not an arc of CG.  The remaining a_2 + 2a_3 non-critical
runs lie in **path** components; for those, TC2 alternation puts the emitter at
position i and the entered head at position i+1 of the *same path component*,
so both endpoints are free chains and the arc is an arc of CG.  Each of the X4h
cost->=4 joins is a single transition from a chain ender to a chain head, both
of which lie in path components at Z = 0 (a cycle link-path's exit is its CNL,
TC3.3, never a heavy), so it too is an arc of CG.  Hence

    |E(CG)| = a_2 + 2a_3 + X4h = |V(CG)| − 1 ,                          (E)

with no arc having an endpoint outside V(CG).

**This is the step that the printed vertex set breaks.**  Under "not forced
singletons", the a_3 middle link-paths (TC3.4) and, when b_q1 = 1, q_1's path
(TC3.5) are deleted, yet 2a_3 of the span arcs have an a_3 middle chain as an
endpoint and q_1's span arc has q_1's chain as its tail.  a_3 + b_q1 arcs are
then left dangling and (E) fails.

### 2.3 Degrees, source, sink

*In-degree <= 1.*  An arc into B is a transition landing on the head crit of B's
first link-path.  By F1 each run start is entered by at most one transition, so
B receives at most one arc.

*Out-degree <= 1.*  An arc out of A is A's ender's completion exit.  By TC1-end
each chain ender has exactly one completion exit, or none if it is the global
end.  So A emits at most one arc.

*Unique source, unique sink.*  By TC1-end the only chain head not entered by a
ps-hit or a cost->=4 heavy is q_1's, and the only ender with no completion exit
is the global end's.  Both are free chains: q_1's path lies in a *path*
component (a cycle has no source, F3/TC2), and the global-end path likewise
(the last class of the ordering ends no cycle: every cycle link-path emits a
CNL, TC3.3).  So in CG the unique in-degree-0 vertex is q_1's chain and the
unique out-degree-0 vertex is the global-end chain.

**Check on the two chain classes the correction newly admits.**

* *a_3 middle chains.*  The middle link-path of a three-block component is at
  position 2 of 3, so by TC3.1 it is ps-entered (in-degree exactly 1, the span
  arc from the chain ending with position 1) and by TC3.2 it emits the CNL into
  the second non-critical run (out-degree exactly 1, the span arc to the chain
  headed by position 3).  It is an ordinary degree-(1,1) interior vertex.  It
  neither creates a source nor a sink and it admits exactly the arcs the
  inventory assigns to it.  **No step fails.**
* *q_1's chain when b_q1 = 1.*  q_1's path is position 1 of a component with
  m >= 2, so by F3 its head is entered by nothing (in-degree 0) and by TC3.2 it
  emits the CNL into the component's first non-critical run (out-degree 1).  It
  is precisely the source of the linear path.  **No step fails**; on the
  contrary, part (1) is only *true* because this vertex is present.

### 2.4 One path plus vertex-disjoint loops

CG has in- and out-degree <= 1, so it is a partial-functional digraph; its
underlying components are directed paths and directed cycles, pairwise
vertex-disjoint.  With |E| = |V| − 1 (E) the number of path components is
|V| − |E| = 1.  Its source is q_1's chain and its sink the global-end chain
(2.3).  Hence:

> CG = one directed path from q_1's chain to the global-end chain, together
> with vertex-disjoint directed cycles ("closure loops").

*Defect class (15,0,1), e = 2.*  TC1z gives NCh = 2 + zh + zp3 = 3, and K2 pins
the skeleton to two wirings, each with exactly one two-block component, one
defect piece and **no cycles** — so every chain is free, |V| = 3, and the arcs
are the one span arc plus the one defect arc, |E| = 2 = |V| − 1.  Same
conclusion.

*Remark (why the cycle chains must be excluded).*  If one instead put **all**
NCh chains in the graph, TC3.3 gives every cycle component its own closed
sub-digraph: a type-I cycle is a single chain with a self-loop, a type-II cycle
a 2-cycle.  The graph would then be one path plus (c_1 + c_2) *trivial*
component-internal loops plus the genuine loops.  Those trivial loops carry no
search branching — the cycles are placed by the endgame exact cover — which is
exactly why the definition removes them.  `checks/cgcheck.py` reports them as
"arcs touching cycle chains (dropped)": 25 on the verified 872, 25–26 on each
counterexample object, matching c_1 + 2c_2 in every case.

### 2.5 Every loop needs a span or defect arc

Write t(A) for the ordering position of y_C, C the last class of A's last
link-path.  If A -> B is a d4 arc it is a single transition: A's ender's
completion exit at position t(A) lands at position t(A)+1 on crit(C') =
rot(y_{C'}) for C' the head class of B's first link-path (TC1-end).  Since
rot(y_{C'}) belongs to C' and y_{C'} is the temporally last member of C',
pos(y_{C'}) > t(A).  Positions increase strictly along link-paths (P3) and
across hops, so t(B) >= pos(y_{C'}) > t(A).  A loop of d4 arcs only would give
t(A) < t(A).  Hence every closure loop contains at least one span arc or the
defect arc.  Loops are vertex-disjoint, hence arc-disjoint, and the number of
span/defect arcs is

    U := a_2 + 2a_3   (Z = 0),      U := 1 + 1 = 2   (defect class),

so **the number of closure loops is at most U**.

(The sharper bound `#loops <= a_2 − b_q1 + 2a_3 (+bn)` of R-n6-9 §1(d) also
holds — q_1's span arc leaves an in-degree-0 vertex and so lies on the linear
path, never on a loop — and is what mysweep.c actually budgets.  The paper does
not need it; it is worth a footnote.)

### 2.6 Statement that is actually true

Parts (1), (2), (3) of the printed lemma are all correct **once the vertex set
is read as "chains not lying in pointer cycles"**.  No additional hypothesis is
required.  In particular the lemma needs no restriction to a_3 = 0 or
b_q1 = 0.

## 3. THE TWO-LOOP BOUND IS INDEPENDENT OF THE VERTEX SET

`approaches/n6coverage/coverage.md` §5.2 proves

    D >= Delta_1 + 6a_2 + 12a_3 + c_1 + 7c_2                      (floors)
    c_1 = e − a_2 − 2a_3 − 2c_2                                   (I-b)
  =>  5 LAMBDA_L <= D − e − Delta_1 <= D − e,  LAMBDA_L := a_2 + 2a_3 + c_2,

then splits the sixteen classes, and kills the residual (20,0,0), e in {3,4,5},
U = 3 corner with the run cap n45 <= 4(nS + LAM).

**Every quantity in that proof is a configuration count — a_2, a_3, c_1, c_2, e,
D, Delta_1, nS, n45, LAM.  CG does not appear.**  The proof bounds
U = a_2 + 2a_3, which by §2.2 is the number of span arcs — an *arc* count fixed
by the pointer components, not by which chains are called vertices.  The
correction therefore leaves §5.2 **verbatim intact**; it does not have to be
redone.

(The one place where the vertex set matters at all is the claim that those U
arcs are arcs *of CG*, i.e. that both endpoints are vertices.  Under the
corrected definition that is true — §2.2.  Under the printed one it is false
for a_3 + b_q1 of them, which is a further reason the printed version cannot be
patched by adjusting the count alone.)

Machine audit unchanged: `approaches/n6coverage/checks/loopbound.py` brute-forces
all integer tuples admitted by the weakened system (both ledgers off) and
reports max U = 2 over all fifteen Z = 0 classes.

## 4. DOWNSTREAM AUDIT — every consumer of Lemma 6.8

Citations of `lem:closure` in `report/PAPER-n6-872.tex`:

| line | use | survives verbatim? |
|---|---|---|
| 174 | intro: "a closure-topology lemma that bounds how the …" | YES — no vertex set mentioned |
| 1479 | "for the 480 instances whose configuration admits a loop … over every anchored loop structure permitted by Lemma 6.8" | YES — uses only part (1)+(3), the *shape* and the loop count |
| 1497 | "planted instances exercising every closure kind of Lemma 6.8" | YES — arc kinds, unchanged |
| 1687 | Coverage Theorem step (e): "Sigma's closure graph is one path plus at most two vertex-disjoint loops … the other 151 instances have U = 0 and are provably linear" | YES — parts (1),(3) only.  "U = 0 ⟹ linear" is §2.5 (no span/defect arc ⟹ no loop), which needs the *arc* count, not the vertex set |
| 1782 | audit table row for part (3) | YES |
| 1856, 1864, 1872 | Algorithm 6 / remark on the previously-asserted bound | YES |
| 2516 | Algorithm 6 completeness: "the closure structures searched … cover all closure structures a real candidate can induce" | YES — and it is *strengthened*: with q_1's chain restored as a vertex, the engine's `m2n > (in_loop ? 0 : bq1)` reservation is exactly the lemma's "q_1's chain is the source, its arc is on the linear path" |

`approaches/n6coverage/coverage.md` §6.2(e) is the same argument and is
likewise untouched; §5.1–5.4 there already carry the corrected definition, so
nothing in coverage.md needs editing.

**No consumer needs, or is even compatible with, the printed vertex set.**
Under the printed set, step (e) at line 1687 would be *false* whenever b_q1 = 1:
the five b_q1 = 1 jobs identified in R-n6-9 §1(d) would have a closure graph
with no source at all.

## 5. CONTROLS

### 5.1 Real objects — `checks/cgcheck.py`, `logs/cgreal.log`

Independent builder: link-paths, chains, pointer components and the census come
from the R-n6-7 reviewer's own analyzer (`reviews/R-n6-7-workdir/myanalyze.py`,
written from raw definitions); CG itself — vertex set, arc inventory, arc
typing, decomposition — is built fresh in `cgcheck.py`.  Checked for every
object: |V| = a_2+2a_3+1+X4h, |E| = a_2+2a_3+X4h, no arc leaving V, in-/out-
degree <= 1, exactly one source and one sink, k loops with k <= U, and every
loop carrying a non-d4 arc.

| object | L | e | X4h | (a_1,a_2,a_3,c_1,c_2) | NCh | \|V\| = pred | \|E\| | **k** | U | all clauses |
|---|---|---|---|---|---|---|---|---|---|---|
| `shared/best872.txt` | 872 | 25 | 0 | (4,0,0,25,0) | 26 | 1 = 1 | 0 | **0** | 0 | PASS |
| 96 × `optimal-873/sol*.txt` | 873 | 0 | 5 | (24,0,0,0,0) | 6 | 6 = 6 | 5 (all d4) | **0** | 0 | PASS (96/96) |
| `m2obj_620_23` | 877 | 27 | 0 | (6,1,0,26,0) | 28 | 2 = 2 | 1 | **1** | 1 | PASS |
| `m2obj_620_1` | 877 | 29 | 0 | (2,3,0,26,0) | 30 | 4 = 4 | 3 | **3** | 3 | PASS |
| `m2obj_620_0` | 878 | 29 | 0 | (2,4,0,25,0) | 30 | 5 = 5 | 4 | **4** | 4 | PASS |
| `m2obj_620_14` | 878 | 29 | 0 | (2,4,0,25,0) | 30 | 5 = 5 | 4 | **4** | 4 | PASS |
| `m2obj_620_19` | 878 | 29 | 0 | (2,4,0,25,0) | 30 | 5 = 5 | 4 | **4** | 4 | PASS |
| `m2obj_620_11` | 880 | 30 | 0 | (2,5,0,25,0) | 31 | 6 = 6 | 5 | **5** | 5 | PASS |

**103 objects, 0 violations.**  The vertex count matches
a_2 + 2a_3 + 1 + X4h exactly in every one.

Measured loop counts k = 0 (872), 0 (all 96 × 873), and 1, 3, 4, 4, 4, 5 on the
six counterexample objects — i.e. exactly the multiset {1,3,4,4,4,5} the paper's
remark after Lemma 6.8 reports as the realised U values, and here k = U in all
six (every span arc is used by a loop).  Every one of those loops has length 1:
a chain closing its own two-block component (the "zero-arc self-closing span"
of R-n6-9 §2).  On the 872 the 25 dropped arcs are exactly the 25 type-I cycle
self-loops of §2.4's remark; on each counterexample object the dropped count is
c_1 + 2c_2 (25 or 26) as predicted.

### 5.2 HONEST NEGATIVE, and how it is covered

**Every real object available has a_3 = 0 and b_q1 = 0.**  (Measured: q_1's
pointer component has m = 1 in all 103.)  On such objects the two definitions
*coincide* — they differ by a_3 + b_q1 — so §5.1, on its own, cannot
discriminate between them.  It confirms the corrected count; it does not by
itself refute the printed one.

The discrimination is supplied by `checks/cgabstract.py`
(`logs/cgabstract.log`), which builds the abstract chain/arc structure of a
configuration **directly from TC1-end + TC3** (the only facts the lemma uses),
for configurations that *do* have a_3 > 0 and/or b_q1 = 1, wires the free
choices at random, and evaluates Lemma 6.8's claims under both vertex sets.
276 configurations × 20 random wirings = 5520 trials:

```
A  CORRECTED  V = chains not lying in pointer cycles   : 5520/5520 pass
B  AS PRINTED V = chains that are not forced singletons:  960/5520 pass
   B failures keyed by (a3>0, b_q1=1): {(True,False):1920, (True,True):1920, (False,True):720}
```

B passes exactly the 960 trials with a_3 = 0 **and** b_q1 = 0 — i.e. exactly
where the two definitions agree — and fails every single trial where they
differ.  Witness (a_1,a_2,a_3,c_1,c_2,X4h,b_q1) = (11,1,1,2,0,1,1), U = 3:

```
A: |V|=5 (pred 5)  |E|=4  dangling 0  sources 1  sinks 1  source = q1's chain  k=1   PASS
B: |V|=3 (pred 5)  |E|=1  dangling 3  sources 2  sinks 2  source != q1's chain  k=1  FAIL
```

Caveat, stated plainly: the abstract model has no notion of ordering position,
so a random wiring can produce a d4-only loop, which the temporal argument of
§2.5 forbids in a real ordering.  The `k <= U` clause is therefore waived on
exactly those 1222 trials; every trial with k > U was one of them (149/149), so
the waiver is not hiding a counterexample.

### 5.3 Symbolic — `checks/symbolic.py`, `logs/symbolic.log`

Over all (a_2,a_3,c_1,c_2,X4h,b_q1) in a box: `ch − (c_1+2c_2)` is identically
`a_2+2a_3+1+X4h` (the proof's count) and `ch − (c_1+2c_2+a_3+b_q1)` is
identically LAMBDA `= a_2+a_3+1+X4h−b_q1` (the TC4 quantity), the two differing
by a_3 + b_q1.  Confirms the coordinator's arithmetic and identifies the source
of the transcription error: §6.2's forced-singleton ledger was carried into
§6.3 where the cycle-chain exclusion belonged.

## 6. DROP-IN LATEX

Replace lines 1360–1381 of `report/PAPER-n6-872.tex` (the `lemma` environment)
and lines 1396–1409 (part (1) of the proof) with the following.  Parts (2) and
(3) of the proof and the surrounding remarks are unchanged.

```latex
\begin{lemma}[Closure topology]\label{lem:closure}
Call a hop-chain a \emph{cycle chain} if its link-paths lie in a pointer
cycle component and a \emph{free chain} otherwise; by
Lemma~\ref{lem:cyclefive} every cycle link-path is a singleton chain, so
the two classes partition the $\NCh$ chains and there are $c_1+2c_2$
cycle chains.  Consider the directed graph $CG$ whose vertices are the
\emph{free} chains of a candidate, and whose arcs record ``the end of
chain $A$ triggers the head of chain $B$'' (by closing a two-block or
three-block component, by a cost-$\ge 4$ join, or by the defect join in
the class of Lemma~\ref{lem:zclass}).  Then:
\begin{enumerate}
\item $CG$ is a disjoint union of one directed path --- from the chain
  of $q_1$ to the chain containing the global end --- and
  vertex-disjoint directed cycles (``closure loops'').
\item Every closure loop contains at least one arc routed through a
  non-critical run of a path component, or the defect arc; the number
  of such arcs is $U:=a_2+2a_3$ at $Z=0$ and $U:=2$ in the defect
  class.
\item $U\le 2$ in every one of the sixteen classes of
  Theorem~\ref{thm:classes}, and the bound is attained.  Hence every
  candidate's closure structure is the linear path together with at
  most \emph{two} closure loops.
\end{enumerate}
\end{lemma}
```

and, for part (1) of the proof:

```latex
(1)  Every link-path lies in exactly one pointer component
(Lemma~\ref{lem:alternation}), and by Lemma~\ref{lem:cyclefive} a cycle
link-path is both entered by a premature-exit hit and the emitter of a
completion non-link, hence both heads and ends its chain: it is a
singleton chain.  So no chain mixes cycle and path link-paths, the
cycle chains number $c_1+2c_2$, and by Lemma~\ref{lem:chaincount} and
\eqref{eq:Ib}
\[
|V(CG)|=\NCh-(c_1+2c_2)=(e+1+X4h)-(c_1+2c_2)=a_2+2a_3+1+X4h .
\]
The arc inventory is exact.  Each of the $e$ non-critical runs receives
exactly one completion non-link and generates exactly one premature-exit
hit, giving one candidate arc each.  Of those runs, $c_1+2c_2$ lie in
cycles by \eqref{eq:Ib}, and for those both the emitting and the entered
link-path are cycle paths, hence cycle chains and not vertices of $CG$;
the remaining $a_2+2a_3$ lie in path components, where the alternation
of Lemma~\ref{lem:alternation} puts emitter and entered head at
consecutive positions of the \emph{same} path component, so both
endpoints are free chains and each contributes one arc of $CG$.  Each of
the $X4h$ cost-$\ge4$ joins likewise runs between free chains
(a cycle link-path's completion exit is its non-link, never a heavy) and
contributes one arc.  Thus $|E(CG)|=a_2+2a_3+X4h=|V(CG)|-1$, with no arc
leaving $V(CG)$.

By Lemma~\ref{lem:chaincount} each chain head is entered by at most one
transition and each chain end has at most one completion exit, so $CG$
has in- and out-degree at most $1$; the unique head with no in-arc is
$q_1$'s and the unique end with no out-arc is the global end's, and both
lie in path components, hence are vertices of $CG$.  A partial-functional
digraph with $|E|=|V|-1$ is one path --- here from $q_1$'s chain to the
global-end chain --- plus vertex-disjoint cycles.  In the defect class
Lemma~\ref{lem:zclass} gives $\NCh=3$ with no cycle component, so
$|V|=3$ and $|E|=2$, and the same conclusion.
```

Add, next to Remark~\ref{rem:closurefix}:

```latex
\begin{remark}[Vertex set of $CG$]\label{rem:closurevx}
An earlier version of this lemma described $V(CG)$ as ``the chains that
are not forced singletons''.  That is the wrong set: it is
$\Lambda=a_2+a_3+1+X4h-b_{q_1}$, the quantity of
Section~\ref{sec:config}, and it deletes the middle chain of every
three-block component and, when $b_{q_1}=1$, $q_1$'s own chain --- the
latter being the very vertex part~(1) names as the source of the linear
path, and $a_3+b_{q_1}$ of the arcs would be left with an endpoint
outside the graph.  The correct set is the one above, the chains not
lying in pointer cycles, and the count $a_2+2a_3+1+X4h$ printed in the
proof was always the correct one; the rest of the argument, and every
use made of the lemma, is unaffected.  In particular the bound of
part~(3) is a bound on the number of \emph{arcs} $U=a_2+2a_3$ and does
not refer to the vertex set at all.
\end{remark}
```

## 7. FILES

* `src/closure/checks/cgcheck.py` — CG builder + structural checker for real superpermutations.
* `src/closure/checks/cgabstract.py` — abstract TC1-end/TC3 closure-structure generator; A/B discrimination.
* `src/closure/checks/symbolic.py` — the two counts, symbolically.
* `src/closure/logs/cgreal.log`, `src/closure/logs/cgabstract.log`,
  `src/closure/logs/symbolic.log`.

Reproduce:

From the repository root:

```
sh src/closure/run.sh
```

or, individually,

```
python3 src/closure/checks/cgcheck.py data/best872.txt \
    data/counterexamples/m2obj_*.txt \
    data/optimal-873/*.txt
python3 src/closure/checks/cgabstract.py
python3 src/closure/checks/symbolic.py
```

(In this repository the reviewer's analyzer `myanalyze.py`, on which
`cgcheck.py` depends, is vendored at `src/closure/deps/myanalyze.py`; the
object paths above are repo-relative.  Paths named elsewhere in this document
--- `approaches/...`, `reviews/...`, `report/...` --- refer to the working
tree in which the investigation was carried out, not to this repository.)
