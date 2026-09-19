#!/usr/bin/env python3
"""itemB_controls.py -- control-validate Algorithm 2's rejection rules R1-R14
(PAPER-n6-872.tex Appendix A.2) on the verified 872 and the 96 verified 873s.
A rule quantified over all orderings is FALSE if it rejects a real object's own
profile at its own length.  Profiles are extracted by approaches/n6/checks/lib6.py
(which itself asserts the identity stock); the scanner's substitutions
SH := hits, ST := cnl, X4h := X4 are applied exactly as in the paper's ranges.
R13/R14 use the frontier/packing code of approaches/n6-871/checks/scan871.py.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("itemB_controls: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips the `assert` statements of the modules it imports")
import sys, os, glob
# --- repository-portable path setup (added when vendoring into the public
# repository; the audit workspace originals resolved these against the
# project tree).  LIB holds lib6.py / scan871.py / validate871.py; DATA holds
# best872.txt and optimal-873/sol*.txt. ---
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
LIB  = _os.path.join(_HERE, _os.pardir, 'lib')
DATA = _os.path.abspath(_os.path.join(_HERE, _os.pardir, _os.pardir, _os.pardir, 'data'))
_sys.path.insert(0, LIB)
P872 = _os.environ.get('SUPERPERM_P872') or _os.path.join(DATA, 'best872.txt')
# SUPERPERM_P872 substitutes another length-872 witness in the 872 slot of
# the control corpus; see ../../external-872-control/.
G873 = _os.path.join(DATA, 'optimal-873', 'sol*.txt')
# --- end path setup ---
import lib6
import scan871

def rules(o, label):
    L = o.L
    slack = o.slack
    D, X4, Z, e = o.D, o.X4, o.Z, o.e
    zq, zh, zp3, zp2s, zp2g = o.zq, o.zh, o.zp3, o.zp2s, o.zp2g
    Q2, Ncyc, NCh = o.Q2, o.Ncyc, o.NCh
    S5 = sum(1 for p in o.paths if len(p) == 4)
    S4 = sum(1 for p in o.paths if len(p) <= 3)
    X4h = X4              # scanner range sets X4h = X4 (weakest caps; sound)
    P = 24 + D // 5
    h = 23 + D // 5 + Z - e
    Sp, Fp = S5 + S4, P - (S5 + S4)
    cnl = e - (zq + zh + zp2s + zp2g)
    hits = e - Q2 - zp3 - zp2g
    SH, ST = hits, cnl
    fails = []
    def chk(name, ok):
        if not ok: fails.append(name)
    chk("R1", h >= 0)
    chk("R2", cnl >= 0)
    chk("R3", hits >= 0)
    chk("R4", Q2 <= zp2s + slack // 4)
    chk("R5", Ncyc <= e - Q2)
    if Z == 0:
        chk("R6", D >= e + 5 * (e - Q2 - Ncyc))
    chk("R7", max(0, D - 4 * S4) <= S5 <= D - 2 * S4 and Sp <= D
              and (D > 0 or Sp == 0))
    chk("R8", hits <= Sp and cnl <= Sp)
    chk("R9", NCh <= 1 + X4h + zh + cnl and SH <= NCh and ST <= NCh)
    Rcap = 1 + X4h + zh + cnl + S4
    chk("R10", Fp + S5 <= 4 * Rcap and S5 <= 2 * Rcap)
    OV = max(0, SH + ST - Sp)
    PEN = max(OV, Ncyc - zp2g)
    chk("R11", PEN <= NCh)
    chk("R12", P - 2 * D <= 4 * NCh - 2 * (SH + ST) - PEN)
    fs = scan871.Fs(NCh, D, SH, ST, PEN)
    ct = scan871.ct_key(4, 2, 0, 0, 4)
    fc = scan871.FCs(NCh, D, S5, S4, SH, ST, PEN, CT=ct)
    chk("R13", fs is not None and P <= fs and fc is not None and P <= fc)
    Ncomp = P - cnl + Q2 + zp3 + Ncyc
    chk("R14", scan871.groups_feasible(Ncomp, Ncyc, P, e, Fp, S5, S4, D,
                                       zp2g=zp2g, ncsrc=zq + zh + zp2s))
    print(f"{label}: L={L} e={e} D={D} X4={X4} Z={Z} Q2={Q2} Ncyc={Ncyc} "
          f"S5={S5} S4={S4} NCh={NCh} P={P} PEN={PEN} "
          f"-> {'ALL 14 PASS' if not fails else 'FAIL ' + ','.join(fails)}")
    return fails

def load(path):
    o = lib6.from_string(open(path).read())
    o.check_identities()
    return o

bad = 0
b872 = P872
bad += len(rules(load(b872), "verified872"))
sols = sorted(glob.glob(G873))
if len(sols) != 96:
    sys.exit(f"corpus: expected 96 length-873 controls, found {len(sols)}")
for i, f in enumerate(sols):
    fl = rules(load(f), os.path.basename(f))
    bad += len(fl)
print("CONTROL", "PASS: no rule rejects any verified object" if bad == 0
      else f"FAIL: {bad} rule rejections")
sys.exit(0 if bad == 0 else 1)
