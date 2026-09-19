"""scanhigh.py -- NEW guard HIGHE-n6 (= CYC5 + NCFLOW + SHORT3) on top of the
registered T-n6-871 stock.  The guard abstains (returns True) unless the
profile has all Z-pools zero AND Q2 = 0.  Statements proved in
proofhighe.md (shipped alongside this file); summary:
 (1) every pointer cycle has EXACTLY 5 vertices (rho order exactly 5);
 (2) at Z=0, Q2=0 the e premature d=2 exits are e ps-hits whose tails are the
     e nc-runs, bijectively: every nc-run has exactly one cnl in-edge and one
     ps out-edge;
 (3) cycles alternate crit-chains/nc-runs: types T1 = (one length-4 path,
     1 nc), T2 = (two paths of lengths {1,2}, 2 nc); every cycle path is a
     singleton hop-chain (ps-headed, cnl-ended, a=b=1);
 (4) path components: k = m-1 exactly, sum(lens) + m - 1 <= 5;
 (5) a non-cycle ps-headed chain's FIRST path has length <= 3; a non-cycle
     cnl-ended chain's LAST path has length <= 3;
 (6) chain heads partition exactly: 1 q_1 + e ps + X4h heavies; tails:
     1 q_720 + e cnl + X4h heavies.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("scanhigh: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import sys, os, functools, itertools

# ---- guard citations, in scan871.py's convention: every tightening this file
# ---- applies names the clause of HIGHE-n6 that licenses it.
CITES = {
 "SHORT3": "HIGHE-n6 clause (5) (SHORT3; proofhighe.md).  A non-cycle ps-headed "
           "hop-chain's FIRST link-path has length <= 3, and a non-cycle "
           "cnl-ended chain's LAST link-path has length <= 3.  Hence in _ccap a "
           "ps-hit head forces a3 = 1 and a cnl tail forces b3 = 1, which is a "
           "STRICTLY TIGHTER frame than scan871._maxblocks's (a,b), that one "
           "assuming only 'short' = length <= 4.",
 "CYC5":   "HIGHE-n6 clause (1).  Every pointer cycle has exactly 5 vertices.",
 "NCFLOW": "HIGHE-n6 clause (2).  At Z=0, Q2=0 the e premature d=2 exits are e "
           "ps-hits whose tails are the e nc-runs, bijectively.",
 "CHAINRUN": "C6-A / CHAINRUN-n6, via scan871._maxblocks: r <= s4 + 1 - a3 - b3 "
           "maximal {4,5}-runs, each of at most RUNCAP=4 paths of which at most "
           "RUNFOURCAP=2 have length 4.",
}
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'class-scanner'))
import scan871 as S


ON = S.DEFAULT | {'paretoS', 'chainrun', 'groups'}

# ---------- (A) group packing: path comps k=m-1; cycles pinned ---------------
@functools.lru_cache(maxsize=None)
def _ptypes():
    T = []
    for m in (1, 2, 3):
        k = m - 1
        for lens in itertools.combinations_with_replacement(range(1, 6), m):
            if sum(lens) + k > 5: continue
            T.append((k, sum(1 for l in lens if l == 5),
                         sum(1 for l in lens if l == 4),
                         sum(1 for l in lens if l <= 3),
                         sum(5-l for l in lens if l <= 3)))
    return tuple(T)

@functools.lru_cache(maxsize=None)
def _pfeas(comps, kk, n5, n4, s4, dfc):
    if comps == 0:
        return kk == 0 and n5 == 0 and n4 == 0 and s4 == 0 and dfc == 0
    if n5 + n4 + s4 < 1 or n5 + n4 + s4 > 3*comps: return False
    if kk + 5*n5 + 4*n4 + (5*s4 - dfc) > 5*comps: return False
    if not (2*s4 <= dfc <= 4*s4): return False
    for (k, d5, d4, ds, dd) in _ptypes():
        if k > kk or d5 > n5 or d4 > n4 or ds > s4 or dd > dfc: continue
        if _pfeas(comps-1, kk-k, n5-d5, n4-d4, s4-ds, dfc-dd): return True
    return False

# ---------- (B) chain economy with forced length<=3 endpoints ----------------
def _mb3(c, s5, s4, a3, b3):
    """CHAINRUN cap with the endpoint length<=3 indicators FIXED to a3,b3.

    This is the inner body of scan871.py:_maxblocks for ONE (a3,b3) pair:
    r <= s4 + 1 - a3 - b3 maximal {4,5}-runs, each of <= RC=4 paths of which
    <= RFC=2 have length 4, so blocks <= s4 + 4r and s5 <= 2r.

    NOTE.  The ONE-block licence of _maxblocks (`best = 1`) is deliberately
    NOT here: it is available only when a == 1 AND b == 1 -- with a single
    non-length-5 path and BOTH endpoints short, the first and last path are
    the same path, so the chain IS that path -- and (a,b) are not arguments
    of this function.  A previous revision applied it for every endpoint
    type and RETURNED it rather than offering it as a floor, which
    under-estimated the cap by up to 6 blocks in the fatal direction; the
    licence is now applied in _ccap, which does know a and b.  Nor is the
    need5/need3 restriction of _maxblocks here (a '4' endpoint needs a
    length-4 path): omitting it can only LOOSEN this upper bound, which is
    the safe direction."""
    if (a3 or b3) and s4 == 0: return None
    r = s4 + 1 - a3 - b3
    if r < 1:
        return s4 if s5 == 0 else None
    if s5 > 2*r: return None
    return s4 + 4*r

@functools.lru_cache(maxsize=None)
def _gS_entry(CT, c, s5, s4, a, b):
    for (cc, t5, t4, ta, tb, tbl) in S.CT_REGISTRY[CT]:
        if (cc, t5, t4, ta, tb) == (c, s5, s4, a, b): return tbl
    return None

@functools.lru_cache(maxsize=None)
def _ccap(CT, c, s5, s4, hps, tcnl):
    """max blocks of ONE chain of cost c with s5 length-4 and s4 length<=3
    paths, whose head is a ps-hit iff hps and tail a cnl iff tcnl."""
    best = None
    for a in ((1,) if hps else (0, 1)):
        for b in ((1,) if tcnl else (0, 1)):
            g = _gS_entry(CT, c, s5, s4, a, b)
            if g is None: continue
            # The CHAINRUN cap for THIS endpoint type, maximised over the
            # length<=3 endpoint indicators, exactly as scan871._maxblocks does.
            # `mb` is seeded with the ONE-block licence, which is available only
            # for a == b == 1 (see _mb3's docstring); as in _maxblocks it is a
            # FLOOR on the maximum, which the (a3,b3) loop may raise.
            mb = 1 if (a and b and s5 + s4 == 1) else None
            # [cite: SHORT3]  hps forces a3 = 1 and tcnl forces b3 = 1.  This
            # is a tightening BEYOND scan871._maxblocks, which is why
            # selfcheck_ccap() below compares only the unrefined frame
            # (hps = tcnl = 0) -- under SHORT3 a smaller cap is correct, not a
            # regression.  MEASURED EXTENT (2026-09-11): relaxing both forcings
            # to (0,1) changes the six target cells from 3/4/2/1/1/1 kept to
            # 4/5/2/1/1/1, and flips (20,0,0) e=5 from CELL DEAD to cell alive.
            # So the e=5 kill of this route DOES rest on SHORT3.  It does not
            # rest on this route: record rows (R5a)/(R5b) state that the whole
            # counting/chain-query route is redundant with the 1111 exhaustive
            # searches of Prop. allempty, which cover (20,0,0) e=1..9 and do not
            # consult this file.  See CERTIFICATES/testbattery/CLOSURE.md.
            for a3 in ((1,) if hps else ((0, 1) if a else (0,))):
                for b3 in ((1,) if tcnl else ((0, 1) if b else (0,))):
                    if a and not a3 and s5 == 0: continue
                    if b and not b3 and s5 == 0: continue
                    m3 = _mb3(c, s5, s4, a3, b3)
                    if m3 is None: continue
                    if mb is None or m3 > mb: mb = m3
            if mb is None: continue
            v = min(g, mb)
            if best is None or v > best: best = v
    return best

@functools.lru_cache(maxsize=None)
def FH(k, m, q5, q4, hs, ts, CT):
    """max total blocks over k chains, total cost m, exactly q5 length-4 and
    q4 length<=3 paths, of which exactly hs have ps heads and ts cnl tails
    (the rest free)."""
    if k == 0:
        return 0 if (m == 0 and q5 == 0 and q4 == 0 and hs == 0 and ts == 0) else None
    if hs > k or ts > k: return None
    best = None
    for hps in ((1,) if hs == k else ((0, 1) if hs else (0,))):
        for tcnl in ((1,) if ts == k else ((0, 1) if ts else (0,))):
            for s4 in range(q4+1):
                for s5 in range(q5+1):
                    lo, hi = s5 + 2*s4, s5 + 4*s4
                    for c in range(lo, min(hi, m)+1):
                        v = _ccap(CT, c, s5, s4, hps, tcnl)
                        if v is None: continue
                        r = FH(k-1, m-c, q5-s5, q4-s4, hs-hps, ts-tcnl, CT)
                        if r is None: continue
                        if best is None or v+r > best: best = v+r
    return best

# ---------- self-check: the economy cap must never fall BELOW the registered one -
def selfcheck_ccap(CT=None):
    """REGRESSION GUARD for the _mb3 defect.

    At the UNREFINED hypotheses (hps = tcnl = 0) _ccap's economy cap ranges over
    exactly the (a,b,a3,b3) combinations scan871._maxblocks does, so it must be
    >= the registered cap for every prescription; a value below it is an
    under-search, and a previous revision of _mb3 produced 1 instead of 7 for
    prescriptions like (c=2,s5=0,s4=1).  Under hps/tcnl = 1 a tighter value is
    intended: those carry the ADDITIONAL hypothesis that a ps-hit head / cnl
    tail forces a length-<=3 first / last path -- HIGHE-n6 clause (5), CITES
    key SHORT3 -- which _maxblocks does not assume, so they are deliberately
    refined and are not compared here.  That clause is load-bearing and is NOT
    checked by any code in this repository; see the note at the forcing site.

    Returns (checked, looser) and raises SystemExit on any violation."""
    if CT is None:
        CT = S.ct_key(S.PARAM('RUNCAP'), S.PARAM('RUNFOURCAP'), S.PARAM('SEPSLOP'),
                      S.PARAM('REFSLOP'), S.PARAM('SINGCOST'))
    RC, RFC, SEP = S.PARAM('RUNCAP'), S.PARAM('RUNFOURCAP'), S.PARAM('SEPSLOP')
    bad, n, looser = [], 0, 0
    for (cc, t5, t4, ta, tb, tbl) in S.CT_REGISTRY[CT]:
        reg = S._maxblocks(cc, t5, t4, ta, tb, RC, RFC, SEP)
        if reg is None: continue
        mb = 1 if (ta and tb and t5 + t4 == 1) else None
        for a3 in ((0, 1) if ta else (0,)):
            for b3 in ((0, 1) if tb else (0,)):
                if ta and not a3 and t5 == 0: continue
                if tb and not b3 and t5 == 0: continue
                m3 = _mb3(cc, t5, t4, a3, b3)
                if m3 is None: continue
                if mb is None or m3 > mb: mb = m3
        n += 1
        if mb is None or mb < reg: bad.append((cc, t5, t4, ta, tb, mb, reg))
        elif mb > reg: looser += 1
    if bad:
        raise SystemExit(f"SELFCHECK FAIL: the chain-economy cap is BELOW the "
                         f"registered scan871._maxblocks in {len(bad)} of {n} "
                         f"prescriptions, e.g. {bad[:3]} -- this UNDER-SEARCHES")
    return n, looser


# ---------- the combined guard ----------------------------------------------
def highe_ok(w, D, X4, Z):
    zq, zh, zp3, zp2s, zp2g = w['pools']
    if zq or zh or zp3 or zp2s or zp2g or w['Q2'] != 0:
        return True                            # abstain: sound fallback
    Pn, e, Ncyc, NCh = w['Pnum'], w['e'], w['Ncyc'], w['NCh']
    S5, S4 = w['S5'], w['S4']
    X4h = w['X4h']
    Fp = Pn - S5 - S4
    Ncomp = Pn - w['cnl'] + Ncyc
    dfc_all = D - S5
    CT = S.ct_key(S.PARAM('RUNCAP'), S.PARAM('RUNFOURCAP'), S.PARAM('SEPSLOP'),
                  S.PARAM('REFSLOP'), S.PARAM('SINGCOST'))
    for c2 in range(0, Ncyc+1):
        c1 = Ncyc - c2
        if S5 < c1 or S4 < 2*c2: continue
        kk = e - (c1 + 2*c2)
        if kk < 0: continue
        dfc = dfc_all - 7*c2
        if dfc < 0: continue
        if not _pfeas(Ncomp - Ncyc, kk, Fp, S5 - c1, S4 - 2*c2, dfc):
            continue
        npin = c1 + 2*c2
        if npin > NCh: continue
        rem_k, rem_m = NCh - npin, D - c1 - 7*c2
        if rem_m < 0: continue
        hs, ts = e - npin, e - npin           # remaining ps heads / cnl tails
        if hs < 0 or hs > rem_k: continue
        v = FH(rem_k, rem_m, S5 - c1, S4 - 2*c2, hs, ts, CT)
        if v is not None and Pn - npin <= v:
            return True
    return False

def run_cells(cells, slack=0):
    out = {}
    for (D, X4, Z, e) in cells:
        ws = S.cell_witnesses(D, X4, Z, e, slack, ON, first_only=False)
        kept = [w for w in ws if highe_ok(w, D, X4, Z)]
        out[(D, X4, Z, e)] = (len(ws), len(kept), kept)
    return out

if __name__ == '__main__':
    _n, _l = selfcheck_ccap()
    print(f"SELFCHECK _ccap: {_n} prescriptions, 0 below the registered "
          f"scan871._maxblocks, {_l} strictly looser (safe)")
    TARGETS = [(20,0,0,e) for e in (5,6,7,8,9)] + [(15,1,0,7)]
    print("== six target cells, L=871 (slack 0) ==")
    for k, (nw, nk, kept) in run_cells(TARGETS).items():
        print(f"  {k}: {nw} profiles -> {nk} after HIGHE  "
              f"[{'DEAD' if nk == 0 else 'alive'}]")
        for w in kept:
            print("     ", {q: w[q] for q in ('Ncyc','S5','S4','NCh','PEN')})
    print("== controls at their own lengths ==")
    for (D,X4,Z,e,sl,name) in [(25,0,0,25,0,'verified-872'),
                               (0,6,0,0,0,'verified-873')]:
        ws = S.cell_witnesses(D, X4, Z, e, sl, ON, first_only=False)
        kept = [w for w in ws if highe_ok(w, D, X4, Z)]
        print(f"  {name} cell ({D},{X4},{Z}) e={e}: {len(ws)} -> {len(kept)} "
              f"({'OK still admissible' if kept else 'EXCLUDED -- BUG OR REFUTED'})")
    print("BUDGET HITS:", S.HITS)
