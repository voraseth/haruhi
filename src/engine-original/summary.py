#!/usr/bin/env python3
# summary.py -- regenerate the K4/K5 verdict tables from the committed logs.
import re, glob
tot_jobs = tot_nodes = tot_sat = tot_cap = 0
for f in sorted(glob.glob('../../CERTIFICATES/campaign-original/realize_*.log')):
    jobs = nodes = sat = cap = 0
    for line in open(f):
        m = re.search(r'\b(SAT|UNSAT)\b nodes=(\d+).*(EXHAUSTED|NODE_CAP_HIT)', line)
        if m:
            jobs += 1; nodes += int(m.group(2))
            if m.group(1) == 'SAT': sat += 1
            if m.group(3) != 'EXHAUSTED': cap += 1
    print(f"{f}: jobs={jobs} nodes={nodes} SAT={sat} capped={cap}")
    tot_jobs += jobs; tot_nodes += nodes; tot_sat += sat; tot_cap += cap
print(f"TOTAL: jobs={tot_jobs} nodes={tot_nodes} SAT={tot_sat} capped={tot_cap}")
