import json, os, random, subprocess, tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from parts import inventory
assets=sorted(inventory(os.environ['GITHUB_REPOSITORY']).values(),key=lambda a:a['size'])
def measure(a):
    with tempfile.TemporaryDirectory() as t:
        p=Path(t)/'part.zst'
        subprocess.run(['curl','-fsSL','--retry','3','-o',p,a['url']],check=True)
        proc=subprocess.Popen(['zstd','-qdc',p],stdout=subprocess.PIPE)
        size=sum(map(len,iter(lambda:proc.stdout.read(1024*1024),b'')))
        if proc.wait(): raise RuntimeError('zstd')
        return size
rng=random.Random(8479);groups=[assets[i*len(assets)//8:(i+1)*len(assets)//8] for i in range(8)]
total=0
with ThreadPoolExecutor(max_workers=4) as pool:
    for group in groups:
        sample=rng.sample(group,min(4,len(group)))
        sizes=list(pool.map(measure,sample))
        total+=sum(a['size'] for a in group)*sum(sizes)/sum(a['size'] for a in sample)
print(f'{len(assets)} published archives, {sum(a["size"] for a in assets)/2**30:.1f} GiB compressed, stratified sample estimates {total/2**30:.1f} GiB tar contents')
