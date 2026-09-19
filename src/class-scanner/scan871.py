"""scan871.py -- INDEPENDENT n=6 Theorem-M corner scanner (T-n6-871).

Written from the lemma STATEMENTS of approaches/n6/proof6.md sections 2-8 and
re-derived here; it shares no code with approaches/n6/checks/scan6.py.  Its job
is (i) to reproduce the registered corner-map ladder L=868..873 -> 0,0,2,8,22,45
as a regression, and (ii) to be the platform on which new n=6 guards are
measured against the eight surviving L=871 corners.

Accounting (n=6, all constants concrete):
    L    = 725 + W + slack,  slack >= 0
    W    = 142 + D/5 + X4 + Z
    h    = 23 + D/5 + Z - e  >= 0
    P#   = 24 + D/5
    W   >= 143                              (imported premise P1-n6)
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("scan871: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import functools, sys


# ---- gate hooks: every guard CONSTANT is resolvable, so the gate's semantic
# ---- teeth can change what a guard MEANS, and its CONDITIONAL teeth can do so
# ---- only outside the regression box.
DEFAULTS = dict(RUNCAP=4, RUNFOURCAP=2, SEPSLOP=0, COMPSIZE=5, KSLOP=0,
                NCOMPSLOP=0, SINGCOST=4, REFSLOP=0, PENSLOP=0, EXACTS45=1,
                T7_BASE=1, SLACKDIV=4, LEMMAC_G2=1)
MUT = {}
COND = None
# A search budget for the two feasibility searches.  Exhausting it makes the
# guard return its WEAKEST answer (feasible / no bound), so the budget can only
# ever ADMIT more profiles: it is sound.  The gate publishes how often it is hit
# and requires ZERO hits in every run that produces a published number.
BUDGET = 30_000_000
NODES = 0
HITS = 0
def budget_reset():
    global NODES, HITS
    NODES = 0; HITS = 0
def PARAM(k, ctx=None):
    if COND is not None:
        v = COND(k, ctx)
        if v is not None: return v
    return MUT.get(k, DEFAULTS[k])

CITES = {
 "PARETOS": "PARETOS-n6.  Write PEN = max(max(0, SH + ST - S_p), Ncyc - zp2g).  At least "
            "PEN of the NCh hop-chains consist of a SINGLE short link-path; such a chain has "
            "exactly 1 block, cost equal to that path's deficiency, which lies in 1..4, and "
            "both endpoint types a = b = 1.",
 "CHAINRUN": "CHAINRUN-n6.  Consider ONE hop-chain.  Let s5 be its number of length-4 "
             "link-paths, s4 its number of link-paths of length <= 3, r its number of maximal "
             "{4,5}-runs of link-paths, a3 = 1 iff its FIRST link-path has length <= 3 and "
             "b3 = 1 iff its LAST one does.",
 "GROUPS": "GROUPS-n6.  Let the pointer graph have Ncomp components, Ncyc of them cycles.",
 "GROUPSI": "(i)   Ncomp = P# - cnl + Q2 + zp3 + Ncyc.",
 "GROUPSII": "(ii)  sum_j l_{g,j} + k_g = #vertices(g) <= 5,",
 "GROUPSIII": "(iii) k_g >= m_g - 1, and k_g >= m_g if g is a cycle,",
 "GROUPSV": "(v)   a component with m_g = 0 has all its internal edges of type zp2g, so",
 "RUNCAP": "C6-A-871 (run caps, re-certified). Every chain all of whose paths have "
           "length in {4,5} has at most",
 "PARETOC": "C6-C-871 (chain Pareto, re-certified). For every cost c <= 16 and endpoint "
            "type (a,b) the maximum number of link-paths in a hop-chain of that cost and type "
            "is g(c,a,b);",
 "REFINED": "C6-S-871 (REFINED chain frontier -- new). For every cost c <= 16, every "
            "s5 >= 0, s4 >= 0 and every endpoint type (a,b), gS(c,s5,s4,a,b) is the maximum "
            "number of link-paths in a hop-chain of cost c that contains exactly s5 paths of "
            "length 4 and exactly s4 of length <= 3 and whose first / last path is short iff "
            "a / b; a combination absent from the table is UNREALIZABLE.",
 "LEMMAC": "LEMMAC-n6 (cycle lemma). Ns >= Ncyc - zp2g: every pointer cycle that contains "
           "a crit-run yields a distinct singleton short hop-chain.",
 "N871A": "THEOREM N871-A. No superpermutation on [6] has length 870.",
}

# ---- the certified n=6 chain constants.  These literals are RE-DERIVED and
# ---- compared entry-for-entry by the gate in every run, from the gate-compiled
# ---- checks/chains871.c: nothing here is trusted.
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
  (24, 23, 23, 22),   # cost 17
  (24, 24, 24, 23),   # cost 18
  (25, 25, 25, 24),   # cost 19
  (25, 25, 25, 25),   # cost 20
]
REFINED_TABLE = [   # (cost, s5, s4, g[0,0], g[1,0], g[0,1], g[1,1]); absent = unrealisable
  (0, 0, 0, 4, -1, -1, -1),
  (1, 1, 0, -1, 4, 4, 1),
  (2, 0, 1, 7, 4, 4, 1),
  (2, 2, 0, -1, -1, -1, 4),
  (3, 0, 1, 7, 4, 4, 1),
  (3, 1, 1, 6, 7, 7, 4),
  (4, 0, 1, 7, 4, 4, 1),
  (4, 0, 2, 10, 7, 7, 4),
  (4, 1, 1, 7, 7, 7, 4),
  (4, 2, 1, -1, 6, 6, 7),
  (5, 0, 2, 10, 8, 8, 5),
  (5, 1, 1, 7, 7, 7, 5),
  (5, 1, 2, 9, 10, 10, 7),
  (5, 2, 1, -1, 7, 7, 7),
  (5, 3, 1, -1, -1, -1, 6),
  (6, 0, 2, 10, 8, 8, 5),
  (6, 0, 3, 11, 10, 10, 7),
  (6, 1, 2, 10, 10, 10, 8),
  (6, 2, 1, 5, 7, 7, 7),
  (6, 2, 2, 10, 9, 9, 10),
  (6, 3, 1, -1, -1, -1, 7),
  (6, 4, 1, -1, -1, -1, 5),
  (7, 0, 2, 10, 8, 8, 5),
  (7, 0, 3, 13, 11, 11, 8),
  (7, 1, 2, 10, 10, 10, 8),
  (7, 1, 3, 12, 11, 11, 10),
  (7, 2, 2, 10, 10, 10, 10),
  (7, 3, 1, -1, 5, 5, 7),
  (7, 3, 2, -1, 10, 10, 9),
  (8, 0, 2, 10, 8, 8, 5),
  (8, 0, 3, 13, 11, 11, 8),
  (8, 0, 4, 14, 11, 11, 10),
  (8, 1, 2, 10, 10, 10, 8),
  (8, 1, 3, 13, 13, 13, 11),
  (8, 2, 2, 10, 10, 10, 10),
  (8, 2, 3, 13, 12, 12, 11),
  (8, 3, 2, -1, 10, 10, 10),
  (8, 4, 1, -1, -1, -1, 5),
  (8, 4, 2, -1, -1, -1, 10),
  (9, 0, 3, 13, 11, 11, 8),
  (9, 0, 4, 15, 14, 14, 11),
  (9, 1, 2, 10, 10, 10, 8),
  (9, 1, 3, 13, 13, 13, 11),
  (9, 1, 4, 15, 14, 14, 11),
  (9, 2, 2, 10, 10, 10, 10),
  (9, 2, 3, 13, 13, 13, 13),
  (9, 3, 2, 9, 10, 10, 10),
  (9, 3, 3, 12, 13, 13, 12),
  (9, 4, 2, -1, 7, 7, 10),
  (10, 0, 3, 13, 11, 11, 9),
  (10, 0, 4, 16, 14, 14, 12),
  (10, 0, 5, 15, 14, 14, 11),
  (10, 1, 3, 13, 13, 13, 11),
  (10, 1, 4, 16, 15, 15, 14),
  (10, 2, 2, 10, 10, 10, 10),
  (10, 2, 3, 13, 13, 13, 13),
  (10, 2, 4, 16, 15, 15, 14),
  (10, 3, 2, 9, 10, 10, 10),
  (10, 3, 3, 13, 13, 13, 13),
  (10, 4, 2, -1, 9, 9, 10),
  (10, 4, 3, -1, 12, 12, 13),
  (10, 5, 2, -1, -1, -1, 7),
  (11, 0, 3, 13, 11, 11, 9),
  (11, 0, 4, 16, 14, 14, 12),
  (11, 0, 5, 17, 15, 15, 14),
  (11, 1, 3, 13, 13, 13, 11),
  (11, 1, 4, 16, 16, 16, 14),
  (11, 1, 5, 16, 15, 15, 14),
  (11, 2, 3, 13, 13, 13, 13),
  (11, 2, 4, 16, 16, 16, 15),
  (11, 3, 2, 8, 10, 10, 10),
  (11, 3, 3, 13, 13, 13, 13),
  (11, 3, 4, 15, 16, 16, 15),
  (11, 4, 2, -1, 9, 9, 10),
  (11, 4, 3, -1, 13, 13, 13),
  (11, 5, 2, -1, -1, -1, 9),
  (11, 5, 3, -1, -1, -1, 12),
  (12, 0, 3, 13, 11, 11, 8),
  (12, 0, 4, 16, 14, 14, 12),
  (12, 0, 5, 19, 17, 17, 15),
  (12, 0, 6, 17, 15, 15, 14),
  (12, 1, 3, 13, 13, 13, 11),
  (12, 1, 4, 16, 16, 16, 14),
  (12, 1, 5, 18, 17, 17, 15),
  (12, 2, 3, 13, 13, 13, 13),
  (12, 2, 4, 16, 16, 16, 16),
  (12, 2, 5, 17, 16, 16, 15),
  (12, 3, 3, 13, 13, 13, 13),
  (12, 3, 4, 16, 16, 16, 16),
  (12, 4, 2, 8, 8, 8, 10),
  (12, 4, 3, 12, 13, 13, 13),
  (12, 4, 4, 16, 15, 15, 16),
  (12, 5, 2, -1, -1, -1, 9),
  (12, 5, 3, -1, 11, 11, 13),
  (13, 0, 4, 16, 14, 14, 12),
  (13, 0, 5, 19, 17, 17, 15),
  (13, 0, 6, 19, 18, 18, 15),
  (13, 1, 3, 13, 13, 13, 11),
  (13, 1, 4, 16, 16, 16, 14),
  (13, 1, 5, 19, 19, 19, 17),
  (13, 1, 6, 18, 17, 17, 15),
  (13, 2, 3, 13, 13, 13, 13),
  (13, 2, 4, 16, 16, 16, 16),
  (13, 2, 5, 19, 18, 18, 17),
  (13, 3, 3, 13, 13, 13, 13),
  (13, 3, 4, 16, 16, 16, 16),
  (13, 3, 5, 17, 17, 17, 16),
  (13, 4, 3, 12, 13, 13, 13),
  (13, 4, 4, 15, 16, 16, 16),
  (13, 5, 2, -1, 8, 8, 8),
  (13, 5, 3, -1, 12, 12, 13),
  (13, 5, 4, -1, 16, 16, 15),
  (13, 6, 3, -1, -1, -1, 11),
  (14, 0, 4, 16, 14, 14, 12),
  (14, 0, 5, 19, 17, 17, 15),
  (14, 0, 6, 22, 19, 19, 18),
  (14, 0, 7, 19, 17, 17, 15),
  (14, 1, 4, 16, 16, 16, 14),
  (14, 1, 5, 19, 19, 19, 17),
  (14, 1, 6, 19, 19, 19, 18),
  (14, 2, 3, 13, 13, 13, 13),
  (14, 2, 4, 16, 16, 16, 16),
  (14, 2, 5, 19, 19, 19, 19),
  (14, 2, 6, 19, 18, 18, 17),
  (14, 3, 3, 13, 13, 13, 13),
  (14, 3, 4, 16, 16, 16, 16),
  (14, 3, 5, 19, 19, 19, 18),
  (14, 4, 3, 12, 13, 13, 13),
  (14, 4, 4, 16, 16, 16, 16),
  (14, 4, 5, 18, 17, 17, 17),
  (14, 5, 3, -1, 12, 12, 13),
  (14, 5, 4, -1, 15, 15, 16),
  (14, 6, 2, -1, -1, -1, 8),
  (14, 6, 3, -1, -1, -1, 12),
  (14, 6, 4, -1, -1, -1, 16),
  (15, 0, 4, 16, 14, 14, 12),
  (15, 0, 5, 19, 17, 17, 15),
  (15, 0, 6, 22, 20, 20, 18),
  (15, 0, 7, 21, 19, 19, 18),
  (15, 1, 4, 16, 16, 16, 14),
  (15, 1, 5, 19, 19, 19, 17),
  (15, 1, 6, 21, 22, 22, 19),
  (15, 1, 7, 19, 19, 19, 17),
  (15, 2, 4, 16, 16, 16, 16),
  (15, 2, 5, 19, 19, 19, 19),
  (15, 2, 6, 20, 20, 20, 19),
  (15, 3, 3, 12, 13, 13, 13),
  (15, 3, 4, 16, 16, 16, 16),
  (15, 3, 5, 18, 19, 19, 19),
  (15, 3, 6, 18, 19, 19, 18),
  (15, 4, 3, 12, 13, 13, 13),
  (15, 4, 4, 16, 16, 16, 16),
  (15, 4, 5, 18, 19, 19, 19),
  (15, 5, 3, 12, 12, 12, 13),
  (15, 5, 4, 14, 16, 16, 16),
  (15, 5, 5, 17, 18, 18, 17),
  (15, 6, 3, -1, 10, 10, 12),
  (15, 6, 4, -1, 13, 13, 15),
  (16, 0, 4, 16, 14, 14, 12),
  (16, 0, 5, 19, 17, 17, 15),
  (16, 0, 6, 22, 20, 20, 18),
  (16, 0, 7, 22, 22, 22, 19),
  (16, 0, 8, 20, 19, 19, 17),
  (16, 1, 4, 16, 16, 16, 14),
  (16, 1, 5, 19, 19, 19, 17),
  (16, 1, 6, 22, 22, 22, 20),
  (16, 1, 7, 21, 21, 21, 19),
  (16, 2, 4, 16, 16, 16, 16),
  (16, 2, 5, 19, 19, 19, 19),
  (16, 2, 6, 22, 21, 21, 22),
  (16, 2, 7, 20, 19, 19, 19),
  (16, 3, 4, 16, 16, 16, 16),
  (16, 3, 5, 19, 19, 19, 19),
  (16, 3, 6, 20, 20, 20, 20),
  (16, 4, 3, 12, 12, 12, 13),
  (16, 4, 4, 16, 16, 16, 16),
  (16, 4, 5, 19, 18, 18, 19),
  (16, 4, 6, 19, 19, 19, 19),
  (16, 5, 3, 12, 12, 12, 13),
  (16, 5, 4, 15, 16, 16, 16),
  (16, 5, 5, 18, 18, 18, 19),
  (16, 6, 3, -1, 12, 12, 12),
  (16, 6, 4, -1, 15, 15, 16),
  (16, 6, 5, -1, 17, 17, 18),
  (16, 7, 3, -1, -1, -1, 10),
  (16, 7, 4, -1, -1, -1, 13),
  (17, 0, 5, 19, 17, 17, 15),
  (17, 0, 6, 22, 20, 20, 18),
  (17, 0, 7, 24, 23, 23, 21),
  (17, 0, 8, 23, 21, 21, 19),
  (17, 1, 4, 16, 16, 16, 14),
  (17, 1, 5, 19, 19, 19, 17),
  (17, 1, 6, 22, 22, 22, 20),
  (17, 1, 7, 22, 22, 22, 22),
  (17, 1, 8, 19, 20, 20, 19),
  (17, 2, 4, 16, 16, 16, 16),
  (17, 2, 5, 19, 19, 19, 19),
  (17, 2, 6, 22, 22, 22, 22),
  (17, 2, 7, 22, 21, 21, 21),
  (17, 3, 4, 16, 16, 16, 16),
  (17, 3, 5, 19, 19, 19, 19),
  (17, 3, 6, 22, 22, 22, 21),
  (17, 3, 7, 19, 20, 20, 19),
  (17, 4, 4, 16, 16, 16, 16),
  (17, 4, 5, 19, 19, 19, 19),
  (17, 4, 6, 21, 20, 20, 20),
  (17, 5, 3, 11, 12, 12, 12),
  (17, 5, 4, 15, 16, 16, 16),
  (17, 5, 5, 18, 19, 19, 18),
  (17, 5, 6, 20, 19, 19, 19),
  (17, 6, 3, -1, 12, 12, 12),
  (17, 6, 4, -1, 16, 16, 16),
  (17, 6, 5, -1, 18, 18, 18),
  (17, 7, 3, -1, -1, -1, 12),
  (17, 7, 4, -1, -1, -1, 15),
  (17, 7, 5, -1, -1, -1, 17),
  (18, 0, 5, 19, 17, 17, 15),
  (18, 0, 6, 22, 20, 20, 18),
  (18, 0, 7, 24, 23, 23, 21),
  (18, 0, 8, 23, 22, 22, 22),
  (18, 0, 9, 22, 20, 20, 19),
  (18, 1, 5, 19, 19, 19, 17),
  (18, 1, 6, 22, 22, 22, 20),
  (18, 1, 7, 24, 24, 24, 23),
  (18, 1, 8, 22, 23, 23, 21),
  (18, 2, 4, 16, 16, 16, 16),
  (18, 2, 5, 19, 19, 19, 19),
  (18, 2, 6, 22, 22, 22, 22),
  (18, 2, 7, 23, 23, 23, 22),
  (18, 2, 8, 20, 20, 20, 20),
  (18, 3, 4, 16, 16, 16, 16),
  (18, 3, 5, 19, 19, 19, 19),
  (18, 3, 6, 22, 22, 22, 22),
  (18, 3, 7, 22, 22, 22, 21),
  (18, 4, 4, 16, 16, 16, 16),
  (18, 4, 5, 19, 19, 19, 19),
  (18, 4, 6, 22, 22, 22, 22),
  (18, 4, 7, 20, 20, 20, 20),
  (18, 5, 4, 16, 16, 16, 16),
  (18, 5, 5, 18, 19, 19, 19),
  (18, 5, 6, 20, 21, 21, 20),
  (18, 6, 3, 11, 11, 11, 12),
  (18, 6, 4, 16, 15, 15, 16),
  (18, 6, 5, 17, 18, 18, 19),
  (18, 6, 6, 19, 20, 20, 19),
  (18, 7, 3, -1, -1, -1, 12),
  (18, 7, 4, -1, 12, 12, 16),
  (18, 7, 5, -1, 15, 15, 18),
  (18, 8, 4, -1, -1, -1, 12),
]

PARETO = {}
for _c,_row in enumerate(PARETO_TABLE):
    for (_a,_b),_v in zip([(0,0),(1,0),(0,1),(1,1)], _row): PARETO[(_c,_a,_b)] = _v
CMAX = len(PARETO_TABLE)-1
ENV = {}
for (_a,_b) in [(0,0),(1,0),(0,1),(1,1)]:
    _best=-1
    for _c in range(CMAX+1):
        _v=PARETO[(_c,_a,_b)]
        if _v>_best: _best=_v
        ENV[(_c,_a,_b)]=_best
REFINED = {}
REFINED_CMAX = max(r[0] for r in REFINED_TABLE)
for _r in REFINED_TABLE:
    for (_a,_b),_v in zip([(0,0),(1,0),(0,1),(1,1)], _r[3:]):
        if _v>=0: REFINED[(_r[0],_r[1],_r[2],_a,_b)] = _v

# The coarse frontier is certified to cost 20 here, but the REGRESSION against
# the registered corner maps must use the REGISTERED constants (cost 16) or it
# is no longer a regression.  CAP_CMAX selects which; callers must reset_caches()
# when they change it.
CAP_CMAX = 20
ENV16 = {}
for (_a,_b) in [(0,0),(1,0),(0,1),(1,1)]:
    _best=-1
    for _c in range(min(16,CMAX)+1):
        _v=PARETO[(_c,_a,_b)]
        if _v>_best: _best=_v
        ENV16[(_c,_a,_b)]=_best

def cap(c, a, b):
    """max link-paths in one hop-chain of cost c whose first/last path is short
    iff a/b: the certified table (running maximum over costs <= c, so the bound
    is monotone) below CMAX, the certified value cap above it."""
    lim = min(CAP_CMAX, CMAX)
    if c <= lim:
        v = (ENV if lim == CMAX else ENV16)[(c,a,b)]
        return None if v < 0 else v
    return 4 - 2*a - 2*b + 2*c                                     # [cite: PARETOC]

@functools.lru_cache(maxsize=None)
def F(k, m, sa, sb):
    """max sum of blocks over k chains of total cost m, at least sa of type a=1
    and at least sb of type b=1."""
    if k == 0:
        return 0 if (m == 0 and sa == 0 and sb == 0) else None
    if sa > k or sb > k: return None
    best = None
    for a in (0,1):
        for b in (0,1):
            for c in range(m+1):
                v = cap(c,a,b)
                if v is None: continue
                r = F(k-1, m-c, max(0,sa-a), max(0,sb-b))
                if r is None: continue
                if best is None or v+r > best: best = v+r
    return best

@functools.lru_cache(maxsize=None)
def Fs(k, m, sa, sb, ns):
    """SAME, but at least ns of the k chains are SINGLE SHORT PATHS: 1 block,
    cost in 1..4, and automatically of type a=b=1."""
    if ns > 0:                                                     # [cite: PARETOS]
        if k == 0 or m < ns: return None
        best = None
        for c in range(1, 5):
            if c > m: break
            r = Fs(k-1, m-c, max(0,sa-1), max(0,sb-1), ns-1)
            if r is None: continue
            if best is None or 1+r > best: best = 1+r
        return best
    return F(k, m, sa, sb)

# ---------------------------------------------------------------- CHAINRUN
# New guard.  Inside ONE hop-chain, write s5 for its number of length-4
# link-paths, s4 for its number of link-paths of length <= 3, and r for its
# number of maximal {4,5}-runs of link-paths.  The s4 short blocks separate the
# runs, so r <= s4 + 1; C6-A (independently certified in logs/chainsA.log:
# MAXBLOCKS=4, MAXFOURS=2, INTERIOR_FOUR=0) caps each run at 4 blocks and 2
# length-4 blocks.  Hence, per chain,
#         blocks <= 4*r + s4 <= 4*(s4+1) + s4 = 5*s4 + 4
#         s5     <= 2*r      <= 2*(s4+1)
# and cost = s5 + (sum of 5-l over the s4 paths), so 2*s4 <= cost-s5 <= 4*s4.
CHAINTYPES = None      # built per corner from the resolved parameters
def _maxblocks(c, s5, s4, a, b, RC=4, RFC=2, SEP=0):
    """Upper bound on the number of link-paths in ONE hop-chain that has cost c,
    exactly s5 link-paths of length 4, exactly s4 of length <= 3, and whose
    first/last link-path is short iff a/b.

    Let r be its number of maximal {4,5}-runs of link-paths.  Write a3 = 1 iff
    its FIRST path has length <= 3 and b3 = 1 iff its LAST one does.  The runs
    are pairwise separated by at least one length-<=3 path, and a leading /
    trailing length-<=3 path is not a separator, so
            s4 >= (r - 1) + a3 + b3,   i.e.   r <= s4 + 1 - a3 - b3.
    Certified C6-A (logs/chainsA.log) caps every run at 4 paths of which at most
    2 have length 4, so
            blocks = s4 + (paths inside runs) <= s4 + 4r,     s5 <= 2r.
    Take the best over the ways an endpoint can be short (length 4 or <= 3)."""
    best = None
    if a == 1 and b == 1 and s5 + s4 == 1:
        best = 1          # a ONE-block chain: its single short path is both ends
    for a3 in ((0,) if a == 0 else ((0,1) if s5 >= 1 else (1,))):
        if a3 == 1 and s4 < 1: continue
        for b3 in ((0,) if b == 0 else ((0,1) if s5 >= 1 else (1,))):
            if b3 == 1 and s4 < 1: continue
            # a '4' endpoint needs a length-4 path there
            need5 = (a == 1 and a3 == 0) + (b == 1 and b3 == 0)
            need3 = a3 + b3
            if s5 < need5 or s4 < need3: continue
            r = s4 + 1 + SEP - a3 - b3
            if r < 1:
                if s5 > 0: continue
                v = s4                      # every path has length <= 3
            else:
                if s5 > RFC*r: continue
                v = s4 + RC*r
            if best is None or v > best: best = v
    return best

@functools.lru_cache(maxsize=None)
def build_chaintypes(Dmax, RC=4, RFC=2, SEP=0, REFSLOP=0, SINGCOST=4):
    """every (cost, s5, s4, a, b, blocks-cap) one hop-chain can have"""
    out = []
    for s4 in range(0, Dmax//2+1):
        for s5 in range(0, Dmax+1):
            lo = s5 + 2*s4; hi = s5 + 4*s4
            for c in range(lo, min(hi, Dmax)+1):
                nsh = s5+s4
                for a in (0,1):
                    for b in (0,1):
                        if (a or b) and nsh == 0: continue
                        cp = cap(c,a,b)
                        if cp is None: continue
                        mb = _maxblocks(c,s5,s4,a,b,RC,RFC,SEP)
                        if mb is None: continue
                        if c <= REFINED_CMAX:
                            rv = REFINED.get((c,s5,s4,a,b))   # [cite: REFINED]
                            if rv is None:
                                if REFSLOP == 0: continue   # profile does not exist
                                rv = 10**6
                            bl = min(cp, mb, rv+REFSLOP)
                        else:
                            bl = min(cp, mb)
                        if a and b and nsh == 1: bl = min(bl,1)
                        if bl < nsh: continue
                        if bl < 1: continue
                        out.append((c,s5,s4,a,b,bl))
    return tuple(out)

CT_REGISTRY = {}
def ct_key(RC,RFC,SEP,RS,SC):
    k=(RC,RFC,SEP,RS,SC)
    if k not in CT_REGISTRY: CT_REGISTRY[k]=build_chaintypes(30,RC,RFC,SEP,RS,SC)
    return k

@functools.lru_cache(maxsize=None)
def FC(k, m, q5, q4, sa, sb, CT=None):
    """max sum of blocks over k chains with total cost m, exactly q5 length-4
    paths and q4 length-<=3 paths, at least sa of type a=1 and sb of type b=1."""
    if k == 0:
        okq = (q5 <= 0 and q4 <= 0) if (q5 < 0 or q4 < 0) else (q5==0 and q4==0)
        return 0 if (m==0 and okq and sa==0 and sb==0) else None
    if sa > k or sb > k: return None
    best = None
    for (c,s5,s4,a,b,bl) in CT_REGISTRY[CT]:
        if c > m or (q5>=0 and s5 > q5) or (q4>=0 and s4 > q4): continue
        r = FC(k-1, m-c, q5-s5 if q5>=0 else -1, q4-s4 if q4>=0 else -1, max(0,sa-a), max(0,sb-b), CT)
        if r is None: continue
        if best is None or bl+r > best: best = bl+r
    return best

@functools.lru_cache(maxsize=None)
def FCs(k, m, q5, q4, sa, sb, ns, CT=None, SINGCOST=4):
    """SAME with at least ns chains forced to be a SINGLE short link-path
    (blocks 1, a=b=1, cost = its deficiency in 1..4)."""
    if ns > 0:
        if k == 0: return None
        best = None
        # a singleton is either a length-4 path (cost 1, s5) or a length<=3 path
        for (c,s5,s4) in [(1,1,0)]+[(cc,0,1) for cc in range(2,SINGCOST+1)]:
            if c > m or (q5>=0 and s5 > q5) or (q4>=0 and s4 > q4): continue
            r = FCs(k-1, m-c, q5-s5 if q5>=0 else -1, q4-s4 if q4>=0 else -1, max(0,sa-1), max(0,sb-1), ns-1, CT, SINGCOST)
            if r is None: continue
            if best is None or 1+r > best: best = 1+r
        return best
    return FC(k, m, q5, q4, sa, sb, CT)


# ---------------------------------------------------------------- GROUPS
# New guard (Z = 0).  The pointer graph decomposes the 120 + e runs into
# Ncomp components; in- and out-degrees are <= 1, so each is a directed path or
# a cycle, and L2 gives every component at most 5 vertices.  Counting edges at
# Z = 0 (links 120-P#, CNLs cnl = e, premature-sig e-Q2) gives
#         Ncomp = P# - cnl + Q2 + zp3 + Ncyc.
# Each component g carries the FULL crit-chains of m_g >= 1 link-paths (a link
# is a pointer edge, so a path's crit-chain never leaves its component; and at
# Z = 0 every nc-run is CNL-entered, whose tail is a crit-run, so no component
# is nc-only) together with k_g nc-runs, and
#         (sum of the m_g path lengths) + k_g = #vertices <= 5.
# A path head crit-run is never link- or CNL-entered, so inside its component
# its in-edge, if any, is a ps-hit whose TAIL is an nc-run; distinct heads use
# distinct nc-runs (out-degree <= 1).  A path component has one source vertex,
# a cycle has none, so
#         k_g >= m_g - 1   (path component),      k_g >= m_g   (cycle).
# Hence the whole multiset of link-path LENGTHS must be partitionable into
# Ncomp such groups.  That is far stronger than DEFSPLIT, which only bounds the
# total deficiency.
@functools.lru_cache(maxsize=None)
def _group_types(CSZ=5, KSLOP=0):
    """(m, cycle_ok, noncycle_ok, k, dn5, dn4, ds4, ddef, dg2_path, dg2_cyc)

    A component carries the FULL crit-chains of m link-paths plus k nc-runs,
    with (sum of the m path lengths) + k = #vertices <= CSZ (= 5 by L2).
    m may be 0 only when the component is nc-only: every internal edge then has
    an nc-run as head AND as tail, i.e. is a premature-sig exit landing on a
    non-crit (a zp2g unit), and if the component is a path its source nc-run has
    no pointer in-edge at all, so it is entered by q_1, by a heavy, or by an
    S-exit landing on a non-crit -- at most zq + zh + zp2s of those exist.
    A path head's in-edge inside its component is a ps-hit whose tail is an
    nc-run, so k >= m - 1 for a path component and k >= m for a cycle."""
    T = []
    def emit(m, lens, k, cyc_ok, ncyc_ok):
        d5 = sum(1 for l in lens if l == 5)
        d4 = sum(1 for l in lens if l == 4)
        ds4 = sum(1 for l in lens if l <= 3)
        dd = sum(5-l for l in lens if l <= 3)
        T.append((m, cyc_ok, ncyc_ok, k, d5, d4, ds4, dd, 0, 0))
    import itertools as _it
    for m in (1,2,3):
        for k in range(0, CSZ+1):
            if k < m-1-KSLOP: continue
            for lens in _it.combinations_with_replacement(range(1,6), m):
                if sum(lens) + k > CSZ: continue
                emit(m, lens, k, k >= m-KSLOP, k >= m-1-KSLOP)
    for k in range(1, CSZ+1):                           # m = 0, nc-only
        T.append((0, k>=2, True, k, 0, 0, 0, 0, k-1, k))
    return tuple(T)

@functools.lru_cache(maxsize=None)
def _gfeas(comps, cyc, kk, n5, n4, s4, dfc, g2, src, CSZ=5, KSLOP=0):
    global NODES, HITS
    NODES += 1
    if NODES > BUDGET:
        HITS += 1
        return True                      # budget exhausted -> weakest answer
    paths = n5+n4+s4
    if comps == 0:
        return (cyc==0 and paths==0 and kk==0 and dfc==0)
    if cyc > comps: return False
    if paths > 3*comps: return False
    if kk + 5*n5 + 4*n4 + (5*s4 - dfc) > CSZ*comps: return False
    if dfc < 2*s4 or dfc > 4*s4: return False
    for (m, cyc_ok, ncyc_ok, k, d5, d4, ds4, dd, gp, gc) in _group_types(CSZ, KSLOP):
        if k > kk or d5 > n5 or d4 > n4 or ds4 > s4 or dd > dfc: continue
        if m > paths: continue
        if m >= 1 and kk - k < (paths - m) - (comps - 1) - KSLOP*comps: continue
        if ncyc_ok and comps-cyc >= 1 and gp <= g2 and (m>=1 or src>=1):
            if _gfeas(comps-1, cyc, kk-k, n5-d5, n4-d4, s4-ds4, dfc-dd,
                      g2-gp, src-(1 if m==0 else 0), CSZ, KSLOP): return True
        if cyc_ok and cyc >= 1 and gc <= g2:
            if _gfeas(comps-1, cyc-1, kk-k, n5-d5, n4-d4, s4-ds4, dfc-dd,
                      g2-gc, src, CSZ, KSLOP): return True
    return False

def groups_feasible(Ncomp, Ncyc, Pnum, e, Fp, S5, S4, D, zp2g=0, ncsrc=0, CSZ=5, KSLOP=0):
    if Ncomp < 1 or Ncyc > Ncomp: return False
    if 120 + e > CSZ*Ncomp: return False
    if Fp < 0 or S5 < 0 or S4 < 0: return False
    if Fp + S5 + S4 != Pnum: return False
    dfc = D - S5
    if dfc < 2*S4 or dfc > 4*S4: return False
    return _gfeas(Ncomp, Ncyc, e, Fp, S5, S4, dfc, zp2g, ncsrc, CSZ, KSLOP)

# ------------------------------------------------------------------ the scan
def corners(B):
    return [(5*k, X4, B-k-X4) for k in range(B+1) for X4 in range(B-k+1)]

def pools(Z):
    for zq in range(min(Z,1)+1):
        r = Z-zq
        for zh in range(r+1):
            for zp3 in range(r-zh+1):
                for zp2s in range(r-zh-zp3+1):
                    yield (zq, zh, zp3, zp2s, r-zh-zp3-zp2s)

GUARDS = ('unit','t1','t2','lemmaS','l12','lu8','defsplit','e1','e2','e3',
          'lemmaC','t7','lemmaR','lemmaA','pareto','paretoS','chainrun','groups')

def cell_witnesses(D, X4, Z, e, slack, on, first_only=True):
    """all admissible profiles for the (corner, e) cell; [] means the cell is
    EMPTY under the guard set `on`."""
    out = []
    k = D//5
    ctx = dict(D=D, X4=X4, Z=Z, e=e, B=k+X4+Z)
    _RC=PARAM('RUNCAP',ctx); _RFC=PARAM('RUNFOURCAP',ctx); _SEP=PARAM('SEPSLOP',ctx)
    _RS=PARAM('REFSLOP',ctx); _SC=PARAM('SINGCOST',ctx)
    _CSZ=PARAM('COMPSIZE',ctx); _KS=PARAM('KSLOP',ctx); _NCS=PARAM('NCOMPSLOP',ctx)
    _PS=PARAM('PENSLOP',ctx); _EX=PARAM('EXACTS45',ctx)
    _T7=PARAM('T7_BASE',ctx); _SD=PARAM('SLACKDIV',ctx); _LC=PARAM('LEMMAC_G2',ctx)
    _CT = ct_key(_RC,_RFC,_SEP,_RS,_SC)
    Pn = 24 + k
    h = 23 + k + Z - e
    if 'unit' in on and h < 0: return out
    for (zq,zh,zp3,zp2s,zp2g) in pools(Z):
        zL = zq+zh+zp2s+zp2g
        cnl = e - zL
        if 't1' in on and cnl < 0: continue
        q2cap = zp2s + (slack//_SD if 'lemmaS' in on else 10**9)
        for Q2 in range(0, min(e, q2cap)+1):
            pshits = e - Q2 - zp3 - zp2g
            if 't2' in on and pshits < 0: continue
            NcycHi = (e - Q2) if 'l12' in on else e
            for Ncyc in range(0, NcycHi+1):
                if 'lu8' in on and Z == 0 and D < e + 5*(e-Q2-Ncyc): continue
                # NEW: every pointer cycle at Z=0 occupies exactly 5 runs, of
                # which k_i >= 1 are nc-runs -> sum over cycles of k_i <= e-Q2
                # already in l12; the cyc5 guard adds the deficiency form.
                for S4 in range(D//2+1):
                    if 'defsplit' in on:
                        if S4 == 0:
                            S5rng = (D,) if D >= 0 else ()
                            if D > 0: S5rng = (D,)
                        else:
                            lo = max(0, D-4*S4); hi = D-2*S4
                            if hi < lo: continue
                            S5rng = range(lo, hi+1)
                    else:
                        S5rng = range(max(0, D-2*S4)+1)
                    for S5 in S5rng:
                        Sp = S5+S4
                        if D == 0 and Sp != 0: continue
                        if Sp > D: continue
                        if 'e1' in on and pshits > Sp: continue
                        if 'e2' in on and cnl > Sp: continue
                        Fp = Pn - Sp
                        if Fp < 0: continue
                        for X4h in range(X4, X4+1):
                            NChcap = (_T7 + X4h + zh + cnl) if 't7' in on else Pn
                            if 'lemmaR' in on:
                                Rcap = 1 + X4h + zh + cnl + S4
                                if Fp + S5 > 4*Rcap: continue
                                if S5 > 2*Rcap: continue
                            NChmax = min(Pn, NChcap)
                            for NCh in range(NChmax, 0, -1):
                                SH, ST = pshits, cnl
                                if SH > NCh or ST > NCh: continue
                                OV = max(0, SH+ST-Sp) if 'e3' in on else 0
                                # [cite: LEMMAC]
                                PEN = max(OV, Ncyc - _LC*zp2g) if 'lemmaC' in on else OV
                                if PEN < 0: PEN = 0
                                if PEN > NCh: continue
                                if 'lemmaA' in on:
                                    if Pn - 2*D > 4*NCh - 2*(SH+ST) - PEN: continue
                                if 'pareto' in on:                  # [cite: PARETOC]
                                    v = F(NCh, D, min(SH,NCh), min(ST,NCh))
                                    if v is None or Pn > v: continue
                                if 'paretoS' in on:                 # [cite: PARETOS]
                                    v = Fs(NCh, D, min(SH,NCh), min(ST,NCh), PEN)
                                    if v is None or Pn > v: continue
                                if 'groups' in on:                  # [cite: GROUPS]
                                    Ncomp = Pn - cnl + Q2 + zp3 + Ncyc + _NCS   # [cite: GROUPSI]
                                    if not groups_feasible(Ncomp,Ncyc,Pn,e,Fp,S5,S4,D,
                                                           zp2g, zq+zh+zp2s, _CSZ, _KS):
                                        continue                    # [cite: GROUPSII]
                                if 'chainrun' in on:                # [cite: CHAINRUN]
                                    if _EX: _q5,_q4 = S5, S4
                                    else:   _q5,_q4 = -1, -1     # bookkeeping off
                                    v = FCs(NCh, D, _q5, _q4, min(SH,NCh), min(ST,NCh),
                                            max(0,PEN-_PS), _CT, _SC)
                                    if v is None or Pn > v: continue
                                w = dict(D=D,X4=X4,Z=Z,e=e,Q2=Q2,Ncyc=Ncyc,S5=S5,S4=S4,
                                         Sp=Sp,X4h=X4h,NCh=NCh,h=h,cnl=cnl,pshits=pshits,
                                         Pnum=Pn,PEN=PEN,pools=(zq,zh,zp3,zp2s,zp2g))
                                out.append(w)
                                if first_only: return out
    return out

def corner_cells(D, X4, Z, slack, on):
    """the surviving e-values of one Theorem-M corner"""
    k = D//5
    alive = []
    for e in range(0, 23+k+Z+1):
        if cell_witnesses(D,X4,Z,e,slack,on):
            alive.append(e)
    return alive

def scan_length(L, on, dead_cells=frozenset()):
    T = L - 725
    res = {}
    for B in range(1, T-142+1):
        W = 142+B; slack = T-W
        if slack < 0: continue
        for (D,X4,Z) in corners(B):
            alive = [e for e in corner_cells(D,X4,Z,slack,on)
                     if (D,X4,Z,e) not in dead_cells]
            if alive: res[(B,slack,D,X4,Z)] = alive
    return res

def reset_caches():
    """drop every memo so that a gate phase with different guard constants
    cannot see, or be slowed by, another phase's tables."""
    F.cache_clear(); Fs.cache_clear(); FC.cache_clear(); FCs.cache_clear()
    _gfeas.cache_clear(); build_chaintypes.cache_clear(); CT_REGISTRY.clear()

DEFAULT = frozenset(('unit','t1','t2','lemmaS','l12','lu8','defsplit','e1','e2',
                     'e3','lemmaC','t7','lemmaR','lemmaA','pareto'))

if __name__ == '__main__':
    import os
    here = os.path.dirname(os.path.abspath(__file__))
    on = DEFAULT
    if len(sys.argv) > 1:
        if 'S' in sys.argv[1]: on = on | {'paretoS'}
        if 'C' in sys.argv[1]: on = on | {'chainrun'}
        if 'G' in sys.argv[1]: on = on | {'groups'}
    print("guards:", sorted(on))
    for L in range(868, 874):
        r = scan_length(L, on)
        print(f"L={L}  corners={len(r)}  cells={sum(len(v) for v in r.values())}")
    print()
    for L in (871,):
        r = scan_length(L, on)
        for kk in sorted(r):
            B,slack,D,X4,Z = kk
            es = r[kk]
            print(f"  L={L} B={B} sl={slack} (D,X4,Z)=({D},{X4},{Z}) P#={24+D//5}  e in {min(es)}..{max(es)} ({len(es)})")
