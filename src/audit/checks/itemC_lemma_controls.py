"""itemC_lemma_controls.py -- control validation for C1 (Lemmas 5.2/5.3/5.4).

Runs the independent lemma validator (n6-871/checks/validate871.py check()),
which asserts EVERY clause of PARETOS-n6 (paper Lemma 5.2), CHAINRUN-n6 (5.3)
and GROUPS-n6 (5.4) -- plus the imported stock -- on real orderings:
  * the verified 872 (shared/best872.txt), and
  * all 96 verified optimal 873s (github-n6-872/data/optimal-873/).
Any lemma certified by this audit MUST hold on these; a violation would mean
the lemma is FALSE (refuted by a real superpermutation)."""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("itemC_lemma_controls: refusing to run under -O / PYTHONOPTIMIZE, which "
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
import validate871 as V

def need(cond, msg):
    """Verdict-bearing check that survives -O (unlike `assert`)."""
    if not cond:
        raise SystemExit(f"CONTROLS FAIL: {msg}")

def load(path):
    s = open(path).read().strip()
    need(set(s) <= set('123456'), f"{path}: characters outside 1..6")
    return s

n = 0
p872 = P872
need(len(load(p872)) == 872, f"{p872}: length is not 872")
o = V.Obj(V.from_string(p872)); V.check(o, 'verified-872'); n += 1
print(f"verified-872: e={o.e} S5={o.S5} S4={o.S4} X4={o.X4} X4h={o.X4h} "
      f"Ncyc={o.Ncyc}")
g873 = sorted(glob.glob(G873))
need(len(g873) == 96, f"expected 96 length-873 controls, found {len(g873)}")
for f in g873:
    need(len(load(f)) == 873, f"{f}: length is not 873")
    o = V.Obj(V.from_string(f)); V.check(o, os.path.basename(f)); n += 1
print(f"96x verified-873: last e={o.e} S5={o.S5} S4={o.S4} X4={o.X4} "
      f"X4h={o.X4h}")
need(n == 97, f"expected 97 orderings in the control corpus, checked {n}")

# THE VERDICT.  validate871.check() records every clause failure by appending to
# V.FAILS and never raises, so the wrapper must READ it: a genuine counterexample
# to Lemmas 5.2/5.3/5.4 on a real object would otherwise print CONTROLS PASS and
# exit 0.  V.TOTALRETR/V.RETRACTION are diagnostics, not verdicts.
if V.FAILS:
    print(f"violations={len(V.FAILS)}")
    seen = set()
    for tag, msg in V.FAILS:
        if msg[:60] in seen: continue
        seen.add(msg[:60]); print(f"   {tag}: {msg}")
    print(f"CONTROLS FAIL: {len(V.FAILS)} clause violations over {n} orderings")
    sys.exit(1)
print("violations=0")
print(f"CONTROLS PASS: {n} orderings, every clause of Lemmas 5.2/5.3/5.4 "
      f"(PARETOS/CHAINRUN/GROUPS) satisfied on all of them")
