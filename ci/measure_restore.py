import collections, concurrent.futures, hashlib, json, math, os, random, shutil, statistics, subprocess, tempfile, time
from pathlib import Path
import parts
from plan import graph, plan
def extract(job):
    n,name,a,mods=job
    parts.unpack(n,name,a,mods)
def main():
    start=time.monotonic()
    src=graph()
    shards=plan(src)['shards']
    index=parts.inventory(os.environ['GITHUB_REPOSITORY'])
    chosen=shards[7783]
    deps=parts.dependencies(chosen['modules'],src[1])-set(chosen['modules'])
    work=[]
    for n,s in enumerate(shards):
        mods=deps.intersection(s['modules'])
        if mods:
            name=parts.asset_name(s['key'])
            work.append((n,name,index[name],mods))
    sample=random.Random(7783).sample(work,256)
    mib=sum(j[2]['size'] for j in sample)/2**20
    print(f'Plan {len(work)} dependencies, sample {len(sample)} archives, {mib:.1f} MiB, metadata {time.monotonic()-start:.1f}s',flush=True)
    for kind,workers in [('thread',4),('thread',12),('process',8),('thread',4)]:
        with tempfile.TemporaryDirectory() as t:
            parts.STATE=Path(t)/'parts'; parts.BUILD=Path(t)/'build'; parts.STATE.mkdir()
            start=time.monotonic()
            cls=concurrent.futures.ThreadPoolExecutor if kind=='thread' else concurrent.futures.ProcessPoolExecutor
            kwargs={}
            if kind=='process':
                import multiprocessing
                kwargs['mp_context']=multiprocessing.get_context('fork')
            with cls(max_workers=workers,**kwargs) as pool:
                list(pool.map(extract,sample))
            elapsed=time.monotonic()-start
            nfiles=sum(1 for p in parts.BUILD.rglob('*.olean'))
            assert nfiles==sum(len(j[3]) for j in sample),nfiles
            print(f'MEASURE {kind} {workers}: {elapsed:.1f}s, compressed {mib/elapsed:.1f} MiB/s end-to-end, {nfiles} oleans',flush=True)
if __name__=='__main__': main()
