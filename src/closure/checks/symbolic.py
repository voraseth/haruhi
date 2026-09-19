#!/usr/bin/env python3
"""The two candidate vertex counts, symbolically, over all small configurations."""
diff=set(); ok=True
for a2 in range(6):
 for a3 in range(6):
  for c1 in range(6):
   for c2 in range(6):
    for X4h in range(4):
     for bq1 in (0,1):
      e=a2+2*a3+c1+2*c2; ch=e+1+X4h
      A=ch-(c1+2*c2)                 # corrected: not in a pointer cycle
      B=ch-(c1+2*c2+a3+bq1)          # as printed: not a forced singleton
      C=a2+2*a3+1+X4h                # the count USED in the proof
      L=a2+a3+1+X4h-bq1              # LAMBDA of TC4 / sect 6.2
      ok &= (A==C) and (B==L)
      diff.add(A-B)
print('ch-(c1+2c2)      == a2+2a3+1+X4h  (the proof s count) :',ok)
print('ch-(c1+2c2+a3+bq1)== LAMBDA = a2+a3+1+X4h-bq1         :',ok)
print('A - B  ranges over  {a3+bq1} :',sorted(diff)[:12],'...' if len(diff)>12 else '')
