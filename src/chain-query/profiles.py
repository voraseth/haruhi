"""profiles.py -- dump ALL admissible profiles of the six target cells
(20,0,0) e=5..9 and (15,1,0) e=7 at L=871 (rung 4, slack=0), under the FULL
registered guard set of T-n6-871 (DEFAULT + paretoS + chainrun + groups).
Read-only use of the registered scanner approaches/n6-871/checks/scan871.py."""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'class-scanner'))
import scan871 as S

ON = S.DEFAULT | {'paretoS', 'chainrun', 'groups'}
CELLS = [(20,0,0,e) for e in (5,6,7,8,9)] + [(15,1,0,7)]
out = {}
for (D,X4,Z,e) in CELLS:
    ws = S.cell_witnesses(D, X4, Z, e, 0, ON, first_only=False)
    key = f"({D},{X4},{Z}) e={e}"
    out[key] = ws
    print(f"{key}: {len(ws)} profiles")
    for w in ws:
        print("   ", {k: w[k] for k in
              ('Q2','Ncyc','S5','S4','X4h','NCh','PEN','cnl','pshits','h','pools')})
with open(os.path.join(HERE, 'profiles.json'), 'w') as f:
    json.dump(out, f, indent=1)
print("BUDGET HITS:", S.HITS)
