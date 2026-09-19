"""itemC_x4h_check.py -- C2 checker (T-n6-auditC).

Compares the executed scanner (scan871.py, which SETS X4h := X4 at line 685)
against TRUE X4h semantics, where X4h ranges over its full feasible set.

Feasible set: every transition has cost d <= 6, so a heavy transition (d >= 4)
has d in {4,5,6} and contributes d-3 in {1,2,3} to X4.  With X4h heavies:
      X4h <= X4 <= 3*X4h,  hence  ceil(X4/3) <= X4h <= X4.
TRUE semantics therefore enumerates X4h in [ceil(X4/3), X4]; a cell is alive
iff SOME (profile, X4h) in that range passes all guards.
(An earlier version of this checker used the window ceil(X4/2)..X4, which
wrongly excluded cost-6 transitions -- these are real: in 123456234615 the
only permutation windows are 123456 at position 1 and 234615 at position 7,
with d = 6.  Widening the patch to the true window leaves the verdict
unchanged; no guard anywhere tests a lower bound on X4h.)

Conservativity claim under test: survivor cells(true) == survivor cells(X4h:=X4)
(equality, because X4h appears only with +1 coefficient on the RHS of the two
caps NChcap and Rcap, so X4h = X4 is the weakest instance).
Controls: verified-872 cell (D,X4,Z)=(25,0,0) e=25 at L=872 and verified-873
cell (0,6,0) e=0 at L=873 must stay admissible under BOTH semantics.
"""
if not __debug__:          # A-9: `python3 -O` / PYTHONOPTIMIZE strips every
    import sys as _s       # `assert`, and the verdicts this file prints depend
    _s.exit("itemC_x4h_check: refusing to run under -O / PYTHONOPTIMIZE, which "
            "strips its 1 `assert` statements")
import sys, os, re, time
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
SCAN = os.path.join(LIB, 'scan871.py')

def load(name, patch):
    src = open(SCAN).read()
    if patch:
        old = "for X4h in range(X4, X4+1):"
        new = "for X4h in range((X4+2)//3, X4+1):"
        assert src.count(old) == 1, "patch anchor not unique"
        src = src.replace(old, new)
    ns = {'__name__': name, '__file__': SCAN}
    exec(compile(src, SCAN, 'exec'), ns)
    return ns

def survivors(ns, L, on):
    ns['reset_caches']()
    return ns['scan_length'](L, on)

def main():
    A = load('scan871_asrun', patch=False)   # X4h := X4  (as executed)
    B = load('scan871_true',  patch=True)    # true-range X4h
    on = A['DEFAULT']                        # includes t7 and lemmaR (the two
                                             # X4h-bearing guards)
    ok = True
    for L in range(868, 874):
        ra = survivors(A, L, on); rb = survivors(B, L, on)
        same = (set(ra) == set(rb)) and all(ra[k] == rb[k] for k in ra)
        na = sum(len(v) for v in ra.values()); nb = sum(len(v) for v in rb.values())
        print(f"L={L}: as-run cells={na}  true-X4h cells={nb}  "
              f"{'IDENTICAL' if same else 'DIFFER'}")
        if not same:
            ok = False
            extra = {k: v for k, v in rb.items() if ra.get(k) != v}
            print("   differing corners:", list(extra)[:10])
    # inclusion check: any cell alive under TRUE semantics must be alive as-run
    # (that is the completeness direction; the converse would only mean the
    #  as-run scan kept junk, which is harmless).
    print()
    # controls at their own lengths, full witness call
    for (L, D, X4, Z, e, name) in [(872, 25, 0, 0, 25, 'verified-872'),
                                   (873,  0, 6, 0,  0, 'verified-873')]:
        sl = 0
        wa = A['cell_witnesses'](D, X4, Z, e, sl, on, first_only=True)
        wb = B['cell_witnesses'](D, X4, Z, e, sl, on, first_only=True)
        s = 'OK' if (wa and wb) else 'CONTROL FAILURE'
        print(f"CONTROL {name} (D,X4,Z)=({D},{X4},{Z}) e={e}: "
              f"as-run={'alive' if wa else 'DEAD'} true={'alive' if wb else 'DEAD'} -> {s}")
        if not (wa and wb): ok = False
    print("\nRESULT:", "PASS -- X4h:=X4 substitution changes no survivor cell; "
          "controls admissible under both semantics" if ok else "FAIL")
    return 0 if ok else 1

if __name__ == '__main__':
    t0 = time.time()
    rc = main()
    print(f"elapsed {time.time()-t0:.1f}s")
    sys.exit(rc)
