#!/usr/bin/env python3
import json, re
B='.'
man={j['idx']: j for j in json.load(open(B+'/manifest.json'))}
res={}
for ln in open(B+'/rerun.log'):
    m=re.match(r'RES (\d+) (\S+) m(\d) expect=(\d+) got: (\w+) nodes=(\d+) closures=(\d+) phaseQ=(\d+) (\w+) => (\w+)', ln)
    if m: res[int(m.group(1))]=dict(verdict=m.group(5),nodes=int(m.group(6)),clo=int(m.group(7)),st=m.group(9),ok=m.group(10))
print(f"results: {len(res)} / manifest {len(man)}")
bad=0
nodes_m0=nodes_m1=0; n_m0=n_m1=0
for idx,j in man.items():
    r=res.get(idx)
    if not r: bad+=1; print("NO RESULT:", idx, j['tag']); continue
    okk = r['verdict']=='UNSAT' and r['nodes']==j['nodes'] and r['clo']==j['closures'] and r['st']=='EXHAUSTED'
    if not okk: bad+=1; print("BAD:", idx, j['tag'], j['nodes'], r)
    if j['mode']==0: n_m0+=1; nodes_m0+=r['nodes']
    else: n_m1+=1; nodes_m1+=r['nodes']
print(f"m0: {n_m0} runs {nodes_m0:,} nodes | m1: {n_m1} runs {nodes_m1:,} nodes")
print("ALL IDENTICAL (verdict+nodes+closures+EXHAUSTED):", bad==0)
