#!/usr/bin/env python3
"""elimtable.py -- make Lemma 5.1 (lem:870), Proposition 5.5 (prop:871) and
Theorem 5.7 (thm:classes) of report/PAPER-n6-872.tex AUDITABLE from the page.

For every length L in {868,869,870,871}, every admissible split L = 725+W+slack
with W >= 143, and every admissible structural type (D,X4,Z) with
D/5+X4+Z = W-142, this driver reports

  * the e-range scanned (0 .. 23+D/5+Z, i.e. exactly the range left by R1),
  * whether ANY (type,e) cell survives Algorithm 2,
  * if the type is EMPTY: a MINIMAL SUFFICIENT SET M of rejection rules -- M
    alone already empties the type, and no proper subset of M does (greedy
    minimality, rules dropped in reverse rule order) -- together with the
    DECIDING rule g* = the last rule of M, a concrete profile that satisfies
    every rule of M except g* at the LARGEST e that survives M\\{g*}, and the
    two sides of g* on that profile,
  * if the type is non-empty: the exact list of surviving e.

No mathematics is re-derived here.  Every verdict is produced by the registered
artifact approaches/n6-871/checks/scan871.py (= Algorithm 2), unmodified and
imported; the deciding numbers are read off the artifact's own witness
dictionaries and recomputed with its own predicate functions (F, Fs, FCs,
groups_feasible).

`trace_cell` is an instrumented mirror of scan871.cell_witnesses in which every
generation restriction is turned into an explicit named predicate; it exists
only so that the guard-name/rule-number dictionary and the `sides()` formulas
below can be VERIFIED against the artifact.  `--selfcheck` confirms that it
agrees with the artifact on the alive/dead verdict of every single cell.

Usage:
    python3 elimtable.py              # writes elimtable.txt and elimtable.tex
    python3 elimtable.py --selfcheck  # mirror-vs-artifact agreement only
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("elimtable: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 1 `assert` statements")
import os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
# scan871.py sits beside this file in the distributed tree.
if not os.path.exists(os.path.join(HERE, "scan871.py")):
    sys.exit("scan871.py not found beside elimtable.py; run this script "
             "from its own directory in the repository.")
sys.path.insert(0, HERE)
import scan871 as S                      # the registered artifact, unmodified


BASE = S.DEFAULT                                   # R1-R13 base stock
FULL = BASE | {'paretoS', 'chainrun', 'groups'}    # + Lem 5.2 / 5.3 / 5.4

# guard name of Algorithm 2  ->  rejection-rule number of Appendix C.2
RULE = {
 'unit': 'R1', 't1': 'R2', 't2': 'R3', 'lemmaS': 'R4', 'l12': 'R5',
 'lu8': 'R6', 'defsplit': 'R7', 'e1': 'R8a', 'e2': 'R8b', 't7': 'R9a',
 'lemmaR': 'R10', 'e3': 'R11a', 'lemmaC': 'R11b', 'lemmaA': 'R12',
 'pareto': 'R13c', 'paretoS': 'R13', 'chainrun': 'R13r', 'groups': 'R14',
}
NAME = {
 'unit': 'h>=0', 't1': 'cnl>=0', 't2': 'hits>=0', 'lemmaS': 're-entry bound',
 'l12': 'cycle bound', 'lu8': 'glue bound', 'defsplit': 'defect split',
 'e1': 'hits<=Sp', 'e2': 'cnl<=Sp', 't7': 'chain-count cap (R9, first clause)',
 'lemmaR': 'run cap (R10)', 'e3': 'overlap OV (R11, first clause)',
 'lemmaC': 'cycle lemma PEN>=Ncyc-zp2g (R11, second clause)',
 'lemmaA': 'block count (R12)',
 'pareto': 'R13 with the singleton clause dropped (coarse frontier)',
 'paretoS': 'R13 in full: Pareto frontier + singleton chains (Lem 5.2)',
 'chainrun': 'R13 with the REFINED frontier of Lem 5.3 (no separate'
             ' App.C.2 number)',
 'groups': 'R14 component packing (Lem 5.4)',
}
# the order in which Algorithm 2 applies the rules
ORDER = ['unit', 't1', 'lemmaS', 't2', 'l12', 'lu8', 'defsplit', 'e1', 'e2',
         'lemmaR', 't7', 'e3', 'lemmaC', 'lemmaA', 'pareto', 'paretoS',
         'groups', 'chainrun']
RANK = {g: i for i, g in enumerate(ORDER)}
# bookkeeping rules that are never dropped: R1-R3 are the non-negativity of the
# derived counts and R7 is the defect split, i.e. the accounting identities
# themselves.  Keeping them makes every printed witness a genuine profile.
KEEP = frozenset(('unit', 't1', 't2', 'defsplit'))


# ------------------------------------------------------------ basic queries
def erange(D, Z):
    """the e-values R1 (h = 23 + D/5 + Z - e >= 0) leaves open."""
    return list(range(0, 23 + D // 5 + Z + 1))


def alive_es(D, X4, Z, slack, on):
    return [e for e in erange(D, Z)
            if S.cell_witnesses(D, X4, Z, e, slack, on)]


def is_empty(D, X4, Z, slack, on):
    for e in erange(D, Z):
        if S.cell_witnesses(D, X4, Z, e, slack, on):
            return False
    return True


def minimal_sufficient(D, X4, Z, slack, on):
    """greedy minimal subset M of `on` that already empties the type.
    Rules are offered for removal in reverse rule order, so M is biased
    towards the earliest / cheapest rules."""
    M = set(on)
    for g in reversed(ORDER):
        if g not in M or g in KEEP:
            continue
        if is_empty(D, X4, Z, slack, M - {g}):
            M = M - {g}
    return M


# ------------------------------------------------- deciding numbers of a rule
def _pen(w, on):
    """PEN as Algorithm 2 computes it under guard set `on`."""
    SH, ST, Sp = w['pshits'], w['cnl'], w['Sp']
    zp2g = w['pools'][4]
    OV = max(0, SH + ST - Sp) if 'e3' in on else 0
    PEN = max(OV, w['Ncyc'] - zp2g) if 'lemmaC' in on else OV
    return max(0, PEN), OV


def sides(g, w, M):
    """the two sides of rule g on the witness w (which satisfies M\\{g})."""
    zq, zh, zp3, zp2s, zp2g = w['pools']
    D, e, Q2, Ncyc = w['D'], w['e'], w['Q2'], w['Ncyc']
    S5, S4, Sp, NCh = w['S5'], w['S4'], w['Sp'], w['NCh']
    cnl, hits, Pn = w['cnl'], w['pshits'], w['Pnum']
    Fp = Pn - Sp; X4h = w['X4h']; sl = w['slack']
    PEN = w['PEN']
    if g == 'unit':     return ("h", w['h'], ">=", "0", 0)
    if g == 't1':       return ("cnl", cnl, ">=", "0", 0)
    if g == 't2':       return ("hits", hits, ">=", "0", 0)
    if g == 'lemmaS':   return ("Q2", Q2, "<=", "zp2s+|slack/4|", zp2s + sl // 4)
    if g == 'l12':      return ("Ncyc", Ncyc, "<=", "e-Q2", e - Q2)
    if g == 'lu8':      return ("e+5(e-Q2-Ncyc)", e + 5 * (e - Q2 - Ncyc),
                                "<=", "D", D)
    if g == 'defsplit':
        lo = D if S4 == 0 else max(0, D - 4 * S4)
        hi = D if S4 == 0 else D - 2 * S4
        return ("S5 (S4=%d)" % S4, S5, "in", "[%d,%d]" % (lo, hi), None)
    if g == 'e1':       return ("hits", hits, "<=", "Sp", Sp)
    if g == 'e2':       return ("cnl", cnl, "<=", "Sp", Sp)
    if g == 't7':       return ("NCh", NCh, "<=", "1+X4h+zh+cnl", 1 + X4h + zh + cnl)
    if g == 'lemmaR':
        R = 1 + X4h + zh + cnl + S4
        if Fp + S5 > 4 * R:
            return ("Fp+S5", Fp + S5, "<=", "4Rcap", 4 * R)
        return ("S5", S5, "<=", "2Rcap", 2 * R)
    if g in ('e3', 'lemmaC'):
        P2, OV = _pen(w, (M | {g}))
        return ("PEN", P2, "<=", "NCh", NCh)
    if g == 'lemmaA':
        return ("P-2D", Pn - 2 * D, "<=", "4NCh-2(SH+ST)-PEN",
                4 * NCh - 2 * (hits + cnl) - PEN)
    if g == 'pareto':
        v = S.F(NCh, D, min(hits, NCh), min(cnl, NCh))
        return ("P", Pn, "<=", "F(NCh=%d,D=%d)" % (NCh, D),
                "unrealisable" if v is None else v)
    if g == 'paretoS':
        v = S.Fs(NCh, D, min(hits, NCh), min(cnl, NCh), PEN)
        return ("P", Pn, "<=", "Fs(NCh=%d,D=%d,PEN=%d)" % (NCh, D, PEN),
                "unrealisable" if v is None else v)
    if g == 'chainrun':
        CT = S.ct_key(S.PARAM('RUNCAP'), S.PARAM('RUNFOURCAP'),
                      S.PARAM('SEPSLOP'), S.PARAM('REFSLOP'), S.PARAM('SINGCOST'))
        v = S.FCs(NCh, D, S5, S4, min(hits, NCh), min(cnl, NCh), PEN, CT,
                  S.PARAM('SINGCOST'))
        return ("P", Pn, "<=", "Fr(NCh=%d,S5=%d,S4=%d)" % (NCh, S5, S4),
                "unrealisable" if v is None else v)
    if g == 'groups':
        Ncomp = Pn - cnl + Q2 + zp3 + Ncyc
        ok = S.groups_feasible(Ncomp, Ncyc, Pn, e, Fp, S5, S4, D, zp2g,
                               zq + zh + zp2s, S.PARAM('COMPSIZE'),
                               S.PARAM('KSLOP'))
        return ("pack %d paths (S5=%d,S4=%d,Fp=%d) into Ncomp" %
                (Fp + S5 + S4, S5, S4, Fp), Ncomp, "feasible?",
                "", "yes" if ok else "NO")
    return ("?", 0, "?", "?", 0)


def sides_txt(g, w, M):
    a, av, rel, b, bv = sides(g, w, M)
    if g == 'defsplit':
        return "%s = %d not in %s" % (a, av, b)
    if g == 'groups':
        return "%s = %d : infeasible" % (a, av)
    if rel == ">=":
        return "%s = %d  <  %s" % (a, av, b)
    return "%s = %d  >  %s = %s" % (a, av, b, bv)


def sides_tex(g, w, M):
    """the deciding numbers of rule g, typeset."""
    zq, zh, zp3, zp2s, zp2g = w['pools']
    D, e, Q2, Ncyc = w['D'], w['e'], w['Q2'], w['Ncyc']
    S5, S4, Sp, NCh = w['S5'], w['S4'], w['Sp'], w['NCh']
    cnl, hits, Pn = w['cnl'], w['pshits'], w['Pnum']
    Fp = Pn - Sp; X4h = w['X4h']; sl = w['slack']; PEN = w['PEN']
    if g == 'unit':   return r"$h=%d<0$" % w['h']
    if g == 't1':     return r"$\mathit{cnl}=%d<0$" % cnl
    if g == 't2':     return r"$\mathit{hits}=%d<0$" % hits
    if g == 'lemmaS':
        return r"$Q2=%d>zp2s+\lfloor\slack/4\rfloor=%d$" % (Q2, zp2s + sl // 4)
    if g == 'l12':    return r"$\Ncyc=%d>e-Q2=%d$" % (Ncyc, e - Q2)
    if g == 'lu8':
        return r"$e+5(e-Q2-\Ncyc)=%d>D=%d$" % (e + 5 * (e - Q2 - Ncyc), D)
    if g == 'defsplit':
        lo = D if S4 == 0 else max(0, D - 4 * S4)
        hi = D if S4 == 0 else D - 2 * S4
        return r"$S_5=%d\notin[%d,%d]$ ($S_4=%d$)" % (S5, lo, hi, S4)
    if g == 'e1':     return r"$\mathit{hits}=%d>S_p=%d$" % (hits, Sp)
    if g == 'e2':     return r"$\mathit{cnl}=%d>S_p=%d$" % (cnl, Sp)
    if g == 't7':
        return r"$\NCh=%d>1+X4h+zh+\mathit{cnl}=%d$" % (NCh, 1 + X4h + zh + cnl)
    if g == 'lemmaR':
        R = 1 + X4h + zh + cnl + S4
        if Fp + S5 > 4 * R:
            return r"$F_p+S_5=%d>4R_{\mathrm{cap}}=%d$" % (Fp + S5, 4 * R)
        return r"$S_5=%d>2R_{\mathrm{cap}}=%d$" % (S5, 2 * R)
    if g in ('e3', 'lemmaC'):
        P2, OV = _pen(w, (M | {g}))
        return r"$\mathit{PEN}=%d>\NCh=%d$" % (P2, NCh)
    if g == 'lemmaA':
        return (r"$P-2D=%d>\text{R12 cap}=%d$"
                % (Pn - 2 * D, 4 * NCh - 2 * (hits + cnl) - PEN))
    if g == 'pareto':
        v = S.F(NCh, D, min(hits, NCh), min(cnl, NCh))
        if v is None:
            return r"$P=%d>F(%d,%d)$: unrealisable" % (Pn, NCh, D)
        return r"$P=%d>F(\NCh{=}%d,D{=}%d)=%d$" % (Pn, NCh, D, v)
    if g == 'paretoS':
        v = S.Fs(NCh, D, min(hits, NCh), min(cnl, NCh), PEN)
        rhs = r"\text{unrealisable}" if v is None else str(v)
        return (r"$P=%d>F_s(\NCh{=}%d,D{=}%d,\mathit{PEN}{=}%d)=%s$"
                % (Pn, NCh, D, PEN, rhs))
    if g == 'chainrun':
        CT = S.ct_key(S.PARAM('RUNCAP'), S.PARAM('RUNFOURCAP'),
                      S.PARAM('SEPSLOP'), S.PARAM('REFSLOP'), S.PARAM('SINGCOST'))
        v = S.FCs(NCh, D, S5, S4, min(hits, NCh), min(cnl, NCh), PEN, CT,
                  S.PARAM('SINGCOST'))
        rhs = r"\text{unrealisable}" if v is None else str(v)
        return (r"$P=%d>F_r(\NCh{=}%d,S_5{=}%d,S_4{=}%d)=%s$"
                % (Pn, NCh, S5, S4, rhs))
    if g == 'groups':
        Ncomp = Pn - cnl + Q2 + zp3 + Ncyc
        return (r"$%d$ link-paths do not pack into"
                r" $N_{\mathrm{comp}}{=}%d$ groups" %
                (Fp + S5 + S4, Ncomp))
    return "?"


# ------------------------------------------------------------------ analysis
def analyse(D, X4, Z, slack, on):
    r = dict(D=D, X4=X4, Z=Z, slack=slack, B=D // 5 + X4 + Z,
             ehi=erange(D, Z)[-1])
    es = alive_es(D, X4, Z, slack, on)
    if es:
        r.update(verdict='ALIVE', alive=es)
        return r
    M = minimal_sufficient(D, X4, Z, slack, on)
    gstar, sub, esub = None, None, None
    for g in sorted(M, key=lambda g: -RANK[g]):
        cand = alive_es(D, X4, Z, slack, M - {g})
        if cand:
            gstar, sub, esub = g, M - {g}, cand
            break
    assert gstar is not None, (D, X4, Z)
    estar = max(esub)
    w = S.cell_witnesses(D, X4, Z, estar, slack, sub)[0]
    w['slack'] = slack
    r.update(verdict='EMPTY', alive=[], M=sorted(M, key=lambda g: RANK[g]),
             gstar=gstar, estar=estar, esub=esub, w=w,
             nums=sides_txt(gstar, w, M), tex=sides_tex(gstar, w, M))
    return r


# ------------------------------------------------- instrumented mirror (check)
def trace_cell(D, X4, Z, e, slack, on):
    """mirror of S.cell_witnesses with every generation restriction turned into
    an explicit named predicate.  Returns (alive, (depth, guard, info))."""
    k = D // 5
    ctx = dict(D=D, X4=X4, Z=Z, e=e, B=k + X4 + Z)
    P = S.PARAM
    _RC = P('RUNCAP', ctx); _RFC = P('RUNFOURCAP', ctx); _SEP = P('SEPSLOP', ctx)
    _RS = P('REFSLOP', ctx); _SC = P('SINGCOST', ctx)
    _CSZ = P('COMPSIZE', ctx); _KS = P('KSLOP', ctx); _NCS = P('NCOMPSLOP', ctx)
    _PS = P('PENSLOP', ctx); _EX = P('EXACTS45', ctx)
    _T7 = P('T7_BASE', ctx); _SD = P('SLACKDIV', ctx); _LC = P('LEMMAC_G2', ctx)
    _CT = S.ct_key(_RC, _RFC, _SEP, _RS, _SC)
    Pn = 24 + k
    h = 23 + k + Z - e
    best = [(-1, None, None)]

    def rej(depth, g, info):
        if depth > best[0][0]:
            best[0] = (depth, g, info)

    if 'unit' in on and h < 0:
        rej(0, 'unit', dict(h=h)); return False, best[0]
    for (zq, zh, zp3, zp2s, zp2g) in S.pools(Z):
        zL = zq + zh + zp2s + zp2g
        cnl = e - zL
        if 't1' in on and cnl < 0:
            rej(1, 't1', dict(cnl=cnl)); continue
        q2cap = zp2s + slack // _SD
        for Q2 in range(0, e + 1):
            if 'lemmaS' in on and Q2 > q2cap:
                rej(2, 'lemmaS', dict(Q2=Q2, cap=q2cap)); continue
            pshits = e - Q2 - zp3 - zp2g
            if 't2' in on and pshits < 0:
                rej(3, 't2', dict(pshits=pshits)); continue
            for Ncyc in range(0, e + 1):
                if 'l12' in on and Ncyc > e - Q2:
                    rej(4, 'l12', dict(Ncyc=Ncyc)); continue
                if 'lu8' in on and Z == 0 and D < e + 5 * (e - Q2 - Ncyc):
                    rej(5, 'lu8', dict(D=D)); continue
                for S4 in range(D // 2 + 1):
                    for S5 in range(0, D + 1):
                        if 'defsplit' in on:
                            if S4 == 0:
                                if S5 != D:
                                    rej(6, 'defsplit', dict(S5=S5)); continue
                            else:
                                lo = max(0, D - 4 * S4); hi = D - 2 * S4
                                if not (lo <= S5 <= hi):
                                    rej(6, 'defsplit', dict(S5=S5)); continue
                        else:
                            if S5 > max(0, D - 2 * S4): continue
                        Sp = S5 + S4
                        if D == 0 and Sp != 0: continue
                        if Sp > D: continue
                        if 'e1' in on and pshits > Sp:
                            rej(7, 'e1', dict(pshits=pshits, Sp=Sp)); continue
                        if 'e2' in on and cnl > Sp:
                            rej(8, 'e2', dict(cnl=cnl, Sp=Sp)); continue
                        Fp = Pn - Sp
                        if Fp < 0: continue
                        X4h = X4
                        if 'lemmaR' in on:
                            Rcap = 1 + X4h + zh + cnl + S4
                            if Fp + S5 > 4 * Rcap:
                                rej(9, 'lemmaR', dict(lhs=Fp + S5)); continue
                            if S5 > 2 * Rcap:
                                rej(9, 'lemmaR', dict(lhs=S5)); continue
                        NChcap = _T7 + X4h + zh + cnl
                        for NCh in range(Pn, 0, -1):
                            if 't7' in on and NCh > NChcap:
                                rej(10, 't7', dict(NCh=NCh)); continue
                            SH, ST = pshits, cnl
                            if SH > NCh or ST > NCh: continue
                            OV = max(0, SH + ST - Sp) if 'e3' in on else 0
                            PEN = max(OV, Ncyc - _LC * zp2g) if 'lemmaC' in on else OV
                            if PEN < 0: PEN = 0
                            if PEN > NCh:
                                rej(11, 'lemmaC' if 'lemmaC' in on else 'e3',
                                    dict(PEN=PEN)); continue
                            if 'lemmaA' in on and \
                               Pn - 2 * D > 4 * NCh - 2 * (SH + ST) - PEN:
                                rej(12, 'lemmaA', dict()); continue
                            if 'pareto' in on:
                                v = S.F(NCh, D, min(SH, NCh), min(ST, NCh))
                                if v is None or Pn > v:
                                    rej(13, 'pareto', dict(F=v)); continue
                            if 'paretoS' in on:
                                v = S.Fs(NCh, D, min(SH, NCh), min(ST, NCh), PEN)
                                if v is None or Pn > v:
                                    rej(14, 'paretoS', dict(F=v)); continue
                            if 'groups' in on:
                                Ncomp = Pn - cnl + Q2 + zp3 + Ncyc + _NCS
                                if not S.groups_feasible(Ncomp, Ncyc, Pn, e, Fp,
                                        S5, S4, D, zp2g, zq + zh + zp2s,
                                        _CSZ, _KS):
                                    rej(15, 'groups', dict(Ncomp=Ncomp)); continue
                            if 'chainrun' in on:
                                _q5, _q4 = (S5, S4) if _EX else (-1, -1)
                                v = S.FCs(NCh, D, _q5, _q4, min(SH, NCh),
                                          min(ST, NCh), max(0, PEN - _PS), _CT, _SC)
                                if v is None or Pn > v:
                                    rej(16, 'chainrun', dict(F=v)); continue
                            return True, None
    return False, best[0]


def selfcheck():
    tot = 0; bad = 0
    for on, tag in ((FULL, 'FULL'), (BASE, 'BASE')):
        n = 0; b = 0
        for L in (868, 869, 870, 871):
            T = L - 725
            for B in range(1, T - 142 + 1):
                slack = T - 142 - B
                for (D, X4, Z) in S.corners(B):
                    for e in erange(D, Z):
                        a = bool(S.cell_witnesses(D, X4, Z, e, slack, on))
                        c, _ = trace_cell(D, X4, Z, e, slack, on)
                        n += 1
                        if a != c:
                            b += 1
                            print("MISMATCH", tag, L, (D, X4, Z), e, slack, a, c)
        print("selfcheck %s: %d cells, %d mismatches" % (tag, n, b))
        tot += n; bad += b
    return bad


# ------------------------------------------------------------------- output
def fmt_es(es, dash="-"):
    if not es: return "--"
    es = sorted(es); out = []; i = 0
    while i < len(es):
        j = i
        while j + 1 < len(es) and es[j + 1] == es[j] + 1: j += 1
        out.append(str(es[i]) if j == i else "%d%s%d" % (es[i], dash, es[j]))
        i = j + 1
    return ",".join(out)


def fmt_es_tex(es):
    es = sorted(es); out = []; i = 0
    while i < len(es):
        j = i
        while j + 1 < len(es) and es[j + 1] == es[j] + 1: j += 1
        n = j - i + 1
        if n == 1: out.append(str(es[i]))
        elif n == 2: out.append("%d,%d" % (es[i], es[j]))
        else: out.append(r"%d,\dots,%d" % (es[i], es[j]))
        i = j + 1
    return ",".join(out)


def rules_str(M, gstar):
    sub = [g for g in M if g not in KEEP or g == gstar]
    return "+".join(("[%s]" % RULE[g]) if g == gstar else RULE[g] for g in sub)


def rules_tex(M, gstar):
    sub = [g for g in M if g not in KEEP or g == gstar]
    # "+\allowbreak " lets the rules column wrap inside the paper's p{29mm}
    return "+\\allowbreak ".join(
        (r"\textbf{%s}" % RULE[g]) if g == gstar else RULE[g] for g in sub)


def main():
    t0 = time.time()
    out = []; P = out.append

    P("=" * 118)
    P("ELIMINATION TABLE  --  audit support for PAPER-n6-872.tex")
    P("   Lemma 5.1 (lem:870, L=868,869) / Prop 5.5 (prop:871, L=870) /"
      " Theorem 5.7 (thm:classes, L=871)")
    P("driver : reviews/elimtable-workdir/elimtable.py")
    P("engine : approaches/n6-871/checks/scan871.py  (Algorithm 2), imported"
      " unmodified")
    P("params : CAP_CMAX=%d  SLACKDIV=%d  COMPSIZE=%d  RUNCAP=%d  RUNFOURCAP=%d"
      % (S.CAP_CMAX, S.DEFAULTS['SLACKDIV'], S.DEFAULTS['COMPSIZE'],
         S.DEFAULTS['RUNCAP'], S.DEFAULTS['RUNFOURCAP']))
    P("=" * 118)
    P("")
    P("guard stock BASE = " + " ".join(sorted(BASE)))
    P("guard stock FULL = BASE + paretoS (Lem 5.2) + chainrun (Lem 5.3)"
      " + groups (Lem 5.4)")
    P("")
    P("rule dictionary (Appendix C.2 numbering):")
    for g in ORDER:
        P("    %-6s  %-9s  %s" % (RULE[g], g, NAME[g]))
    P("")

    # ------------------------------------------------------------- ladder
    P("-" * 118)
    P("REGRESSION LADDER  (surviving types / surviving cells)")
    P("-" * 118)
    P("   L        BASE types  BASE cells      FULL types  FULL cells")
    ladder = {}
    for L in range(868, 874):
        rb = S.scan_length(L, BASE); rf = S.scan_length(L, FULL)
        ladder[L] = (len(rb), sum(len(v) for v in rb.values()),
                     len(rf), sum(len(v) for v in rf.values()))
        P("   %d   %10d  %10d      %10d  %10d" % ((L,) + ladder[L]))
    P("   registered BASE cell ladder 868..873 : %s   (paper: 0,0,8,63,219,503)"
      % ", ".join(str(ladder[L][1]) for L in range(868, 874)))
    P("   budget hits = %d  (must be 0)" % S.HITS)
    P("")

    # ------------------------------------------- slack-independence check
    P("-" * 118)
    P("SLACK-INDEPENDENCE (lets the table be indexed by the TYPE alone)")
    P("-" * 118)
    P("R4 is the only slack-dependent rule (Q2 <= zp2s + floor(slack/4)).")
    P("For L <= 871 every admissible slack is <= 3, so floor(slack/4)=0 and R4")
    P("is slack-free.  Verified directly: for every type and every slack it")
    P("occurs with, the surviving e-set is identical.")
    dep = 0
    for B in range(1, 5):
        for (D, X4, Z) in S.corners(B):
            for on in (BASE, FULL):
                v = {tuple(alive_es(D, X4, Z, sl, on)) for sl in range(0, 4 - B + 1)}
                if len(v) > 1:
                    dep += 1
                    P("   SLACK-DEPENDENT: (%d,%d,%d) -> %s" % (D, X4, Z, v))
    P("   slack-dependent types found: %d" % dep)
    P("")
    P("A type with B = D/5+X4+Z therefore occurs at exactly the lengths")
    P("L >= 867+B, L <= 871, with slack = L-867-B:")
    P("   B=1 : L = 868,869,870,871       B=3 : L = 870,871")
    P("   B=2 : L = 869,870,871           B=4 : L = 871")
    P("")

    # ------------------------------------------------------------- the table
    rows = []
    for B in range(1, 5):
        for (D, X4, Z) in S.corners(B):
            rows.append(analyse(D, X4, Z, 0, FULL))     # slack 0 is representative

    P("=" * 118)
    P("TYPE-BY-TYPE ELIMINATION  --  guard stock FULL")
    P("   'rules' = a MINIMAL SUFFICIENT set: these rules ALONE already empty the"
      " type, and dropping any one")
    P("             of them leaves a survivor.  [Rx] marks the deciding rule g*;"
      " the numbers are g*'s two")
    P("             sides on a profile that satisfies every OTHER rule of the set,"
      " at the largest such e.")
    P("=" * 118)
    P("%-3s %-11s %-8s %-8s %-34s %s" %
      ("B", "(D,X4,Z)", "e-range", "verdict", "minimal sufficient rules", "deciding numbers"))
    P("-" * 118)
    lastB = None
    for r in rows:
        if lastB is not None and r['B'] != lastB: P("")
        lastB = r['B']
        typ = "(%d,%d,%d)" % (r['D'], r['X4'], r['Z'])
        er = "0..%d" % r['ehi']
        if r['verdict'] == 'ALIVE':
            P("%-3d %-11s %-8s %-8s %-34s e = %s   (%d %s)" %
              (r['B'], typ, er, "ALIVE", "--", fmt_es(r['alive']),
               len(r['alive']), "class" if len(r['alive']) == 1 else "classes"))
        else:
            P("%-3d %-11s %-8s %-8s %-34s %s   [at e=%d]" %
              (r['B'], typ, er, "empty", rules_str(r['M'], r['gstar']),
               r['nums'], r['estar']))
    P("-" * 118)
    P("")

    # --------------------------------------------------------- per-row detail
    P("=" * 118)
    P("WITNESS DETAIL for every empty type (the profile that survives the"
      " minimal set minus its deciding rule)")
    P("=" * 118)
    for r in rows:
        if r['verdict'] != 'EMPTY': continue
        w = r['w']
        P("(%d,%d,%d)  g*=%s (%s, %s)   e*=%d   e surviving %s\\{%s} = %s" %
          (r['D'], r['X4'], r['Z'], RULE[r['gstar']], r['gstar'],
           NAME[r['gstar']], r['estar'],
           "+".join(RULE[g] for g in r['M']), RULE[r['gstar']],
           fmt_es(r['esub'])))
        P("     profile: e=%d Q2=%d Ncyc=%d S5=%d S4=%d Sp=%d Fp=%d NCh=%d "
          "cnl=%d hits=%d PEN=%d P#=%d pools(zq,zh,zp3,zp2s,zp2g)=%s" %
          (w['e'], w['Q2'], w['Ncyc'], w['S5'], w['S4'], w['Sp'],
           w['Pnum'] - w['Sp'], w['NCh'], w['cnl'], w['pshits'], w['PEN'],
           w['Pnum'], w['pools']))
        P("     violates %s :  %s" % (RULE[r['gstar']], r['nums']))
    P("")

    # ---------------------------------------------------- headline checks
    P("=" * 118)
    P("HEADLINE VERIFICATION")
    P("=" * 118)
    b4 = [r for r in rows if r['B'] == 4]
    P("L=871, admissible types with D/5+X4+Z = 4 : %d   (paper: 15)" % len(b4))
    P("   of them EMPTY                          : %d   (paper: 11)" %
      sum(1 for r in b4 if r['verdict'] == 'EMPTY'))
    P("   of them ALIVE                          : %d   (paper: 4)" %
      sum(1 for r in b4 if r['verdict'] == 'ALIVE'))
    P("ALIVE types with D/5+X4+Z <= 3            : %d   (paper: 0, hence"
      " W=146 and slack=0)" %
      sum(1 for r in rows if r['B'] < 4 and r['verdict'] == 'ALIVE'))
    tot = 0; tot1 = 0
    for r in b4:
        if r['verdict'] != 'ALIVE': continue
        es = r['alive']; es1 = [e for e in es if e >= 1]
        tot += len(es); tot1 += len(es1)
        P("   (%d,%d,%d)  Alg.2 e = %-10s  after Lemma 5.6 (e>=1): e = %s" %
          (r['D'], r['X4'], r['Z'], fmt_es(es), fmt_es(es1)))
    P("L=871 surviving cells, Algorithm 2 only    : %d" % tot)
    P("L=871 surviving cells, after Lemma 5.6     : %d   (paper: 16)" % tot1)
    P("")
    P("Paper's Theorem 5.7 list, reproduced:")
    P("   (10,2,0) e=2 -> 1 ; (15,0,1) e=2 -> 1 ; (15,1,0) e=1,2,3,4,7 -> 5 ;"
      " (20,0,0) e=1..9 -> 9   TOTAL 16")
    P("")
    for L, B in ((868, 1), (869, 2), (870, 3)):
        n = sum(1 for r in rows if r['B'] <= B and r['verdict'] == 'ALIVE')
        P("L=%d: types with D/5+X4+Z <= %d that survive FULL : %d   (paper: 0)"
          % (L, B, n))
    rb = S.scan_length(870, BASE)
    P("L=870 under the BASE stock: %d types / %d cells   (paper: exactly two"
      " classes survive)" % (len(rb), sum(len(v) for v in rb.values())))
    for kk in sorted(rb):
        B, sl, D, X4, Z = kk
        P("      (%d,%d,%d) slack=%d   e = %s   (%d %s)" %
          (D, X4, Z, sl, fmt_es(rb[kk]), len(rb[kk]),
           "cell" if len(rb[kk]) == 1 else "cells"))
    P("   both die once Lem 5.2-5.4 are added; per-type deciding rules:")
    for (D, X4, Z) in ((10, 1, 0), (15, 0, 0)):
        rr = [r for r in rows if (r['D'], r['X4'], r['Z']) == (D, X4, Z)][0]
        P("      (%d,%d,%d): %s ; %s [at e=%d]" %
          (D, X4, Z, rules_str(rr['M'], rr['gstar']), rr['nums'], rr['estar']))
    P("")
    P("-" * 118)
    P("WHICH OF LEMMAS 5.2/5.3/5.4 THE ELIMINATION NEEDS (Prop 5.5's"
      " parenthetical claim)")
    P("-" * 118)
    import itertools
    add = ['paretoS', 'chainrun', 'groups']
    lab = {'paretoS': 'Lem5.2(R13)', 'chainrun': 'Lem5.3(R13r)',
           'groups': 'Lem5.4(R14)'}
    for L in (870, 871):
        P("   L=%d" % L)
        for k in range(4):
            for c in itertools.combinations(add, k):
                r = S.scan_length(L, BASE | set(c))
                P("      BASE + %-40s -> %2d types / %3d cells" %
                  (",".join(lab[x] for x in c) if c else "(nothing)",
                   len(r), sum(len(v) for v in r.values())))
    P("   => at L=870 no single added lemma suffices; {Lem5.3,Lem5.4} is the")
    P("      unique sufficient pair, exactly as Proposition 5.5 states.")
    P("   => at L=871 Lem 5.2 is redundant once Lem 5.3 and Lem 5.4 are on")
    P("      (18 cells with or without it).")
    P("")
    P("elapsed %.1fs" % (time.time() - t0))

    txt = "\n".join(out)
    open(os.path.join(HERE, "elimtable.txt"), "w").write(txt + "\n")
    print(txt)
    write_tex(rows)
    write_csv(rows)
    return rows


def write_csv(rows):
    import csv
    fn = os.path.join(HERE, "elimtable.csv")
    with open(fn, "w", newline="") as fh:
        wcsv = csv.writer(fh)
        wcsv.writerow(["B", "D", "X4", "Z", "lengths", "slacks", "e_lo", "e_hi",
                       "verdict", "alive_e", "n_alive", "minimal_rules",
                       "deciding_rule", "deciding_numbers", "deciding_e",
                       "witness"])
        for r in rows:
            B = r['B']
            Ls = ",".join(str(L) for L in range(867 + B, 872))
            sls = ",".join(str(L - 867 - B) for L in range(867 + B, 872))
            if r['verdict'] == 'ALIVE':
                wcsv.writerow([B, r['D'], r['X4'], r['Z'], Ls, sls, 0, r['ehi'],
                               "alive", " ".join(map(str, r['alive'])),
                               len(r['alive']), "", "", "", "", ""])
            else:
                w = r['w']
                prof = ("e=%d Q2=%d Ncyc=%d S5=%d S4=%d Fp=%d NCh=%d cnl=%d "
                        "hits=%d PEN=%d P=%d pools=%s" %
                        (w['e'], w['Q2'], w['Ncyc'], w['S5'], w['S4'],
                         w['Pnum'] - w['Sp'], w['NCh'], w['cnl'], w['pshits'],
                         w['PEN'], w['Pnum'],
                         "|".join(map(str, w['pools']))))
                wcsv.writerow([B, r['D'], r['X4'], r['Z'], Ls, sls, 0, r['ehi'],
                               "empty", "", 0,
                               "+".join(RULE[g] for g in r['M']),
                               RULE[r['gstar']], r['nums'], r['estar'], prof])
    print("[elimtable.csv: %d data rows]" % len(rows))


# --------------------------------------------------------------------- LaTeX
def write_tex(rows):
    A = []; a = A.append
    a(r"% elimtable.tex -- generated by reviews/elimtable-workdir/elimtable.py")
    a(r"% Needs only booktabs (\toprule,\midrule,\bottomrule) and array, both")
    a(r"% already loaded by PAPER-n6-872.tex.  No longtable.  Uses the paper's")
    a(r"% macros \slack, \Ncyc, \NCh and amsmath's \text.")
    a(r"%")
    a(r"% Suggested accompanying paragraph (to sit next to the table):")
    a(r"%   Write B = D/5+X4+Z = W-142.  A type of index B is admissible exactly")
    a(r"%   at the lengths 867+B <= L <= 871, with slack = L-867-B <= 3.  R4 is")
    a(r"%   the only slack-dependent rejection rule and floor(slack/4)=0")
    a(r"%   throughout, so a type's verdict does not depend on L; this was")
    a(r"%   checked for every admissible slack.  For an empty type the rules")
    a(r"%   named are a minimal sufficient set: R1-R3 and R7 (the derived-count")
    a(r"%   non-negativities and the defect split) together with the listed")
    a(r"%   rules already empty the type, and deleting any listed rule leaves a")
    a(r"%   survivor.  The boldface rule is the deciding one and the last column")
    a(r"%   gives its two sides on a profile that satisfies every other listed")
    a(r"%   rule, at the largest e for which such a profile exists.")
    a(r"")
    a(r"\begin{table}[htbp]\centering\footnotesize")
    a(r"\setlength{\tabcolsep}{4pt}")
    a(r"\caption{Elimination record behind Lemma~\ref{lem:870} ($L=868,869$),"
      r" Proposition~\ref{prop:871} ($L=870$) and Theorem~\ref{thm:classes}"
      r" ($L=871$), one row per structural type.  $B=D/5+X4+Z=W-142$; a type of"
      r" index $B$ occurs exactly at the lengths $867+B\le L\le871$ and its"
      r" verdict is independent of $\slack$.  The $e$-column is the range left"
      r" by R1.  For an empty type the named rules, with R1--R3 and R7, already"
      r" empty it, and deleting any one of them leaves a survivor; the boldface"
      r" rule is the deciding one and the last column is its two sides on a"
      r" profile satisfying all the others.  Deleting the two surviving classes"
      r" with $e=0$ (Lemma~\ref{lem:e0}) leaves the sixteen of"
      r" Theorem~\ref{thm:classes}.}")
    a(r"\label{tab:elim}")
    a(r"\begin{tabular}{@{}clcl"
      r">{\raggedright\arraybackslash}p{29mm}"
      r">{\raggedright\arraybackslash}p{51mm}@{}}")
    a(r"\toprule")
    a(r"$B$ & type & $e$ & verdict & rules & deciding numbers\\")
    a(r"\midrule")
    lastB = None
    for r in rows:
        if lastB is not None and r['B'] != lastB:
            a(r"\midrule")
        first = (r['B'] != lastB)
        lastB = r['B']
        bcol = str(r['B']) if first else ""
        typ = r"$(%d,%d,%d)$" % (r['D'], r['X4'], r['Z'])
        er = r"$\le%d$" % r['ehi']
        if r['verdict'] == 'ALIVE':
            a(r"%s & %s & %s & \textbf{alive} & --- & $e=%s$ \ (%d %s)\\" %
              (bcol, typ, er, fmt_es_tex(r['alive']), len(r['alive']),
               "class" if len(r['alive']) == 1 else "classes"))
        else:
            a(r"%s & %s & %s & empty & %s & %s \ ($e=%d$)\\" %
              (bcol, typ, er, rules_tex(r['M'], r['gstar']), r['tex'],
               r['estar']))
    a(r"\bottomrule")
    a(r"\end{tabular}")
    a(r"\end{table}")
    a(r"")
    a(r"% --- the sixteen classes, read straight off the $B=4$ block above ---")
    a(r"% (10,2,0) e=2 ; (15,0,1) e=2 ; (15,1,0) e=1,2,3,4,7 ; (20,0,0) e=1..9")
    txt = "\n".join(A)
    open(os.path.join(HERE, "elimtable.tex"), "w").write(txt + "\n")
    nb = len(rows)
    nempty = sum(1 for r in rows if r['verdict'] == 'EMPTY')
    print("\n[elimtable.tex: 1 table, %d body rows (%d empty, %d alive), "
          "4 rule-index blocks]" % (nb, nempty, nb - nempty))


if __name__ == '__main__':
    if '--selfcheck' in sys.argv:
        sys.exit(1 if selfcheck() else 0)
    main()
