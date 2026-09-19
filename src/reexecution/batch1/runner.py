#!/usr/bin/env python3
# R-n6-9 re-run: executes manifest jobs with own build, compares node counts.
import json, subprocess, threading, os, sys
BASE='.'
ENG=BASE+'/mysweep9f'
LOG=BASE+'/rerun.log'
manifest=json.load(open(BASE+'/manifest.json'))
done=set()
if os.path.exists(LOG):
    for ln in open(LOG):
        if ln.startswith('RES '): done.add(int(ln.split()[1]))
todo=[j for j in manifest if j['idx'] not in done]
# big jobs first for better packing
todo.sort(key=lambda j:-j['nodes'])
lock=threading.Lock()
cnt=[0]
def run(j):
    argv=[ENG]+[str(x) for x in j['argv']]
    try:
        r=subprocess.run(argv,capture_output=True,text=True,timeout=14400)
        out=r.stdout.strip().splitlines()[-1] if r.stdout else 'ERR'
    except Exception as ex:
        out='EXC '+str(ex)
    ok='?'
    if 'nodes=' in out:
        got=int(out.split('nodes=')[1].split()[0])
        gotv=out.split()[0]
        ok='MATCH' if (got==j['nodes'] and gotv=='UNSAT') else 'MISMATCH'
    with lock:
        cnt[0]+=1
        with open(LOG,'a') as f:
            f.write(f"RES {j['idx']} {j['tag']} m{j['mode']} expect={j['nodes']} got: {out} => {ok}\n")
from concurrent.futures import ThreadPoolExecutor
with ThreadPoolExecutor(max_workers=8) as ex:
    list(ex.map(run,todo))
with open(LOG,'a') as f: f.write(f"ALLDONE {len(todo)} jobs this pass\n")
