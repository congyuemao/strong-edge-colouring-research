"""Finite exhaustive two-block reconnections and reproducible random gluings."""
from itertools import permutations,combinations
from pathlib import Path
import json,time,random
from research.counterexample_splice import tight_edges,conflict_graph,exact_color

def greedy_color(masks):
    n=len(masks);colors=[-1]*n;forbidden=[0]*n;remaining=(1<<n)-1
    while remaining:
        v=max((i for i in range(n) if remaining>>i&1),
              key=lambda i:(forbidden[i].bit_count(),(masks[i]&remaining).bit_count(),i))
        c=0
        while forbidden[v]>>c&1:c+=1
        colors[v]=c;remaining^=1<<v
        neighbors=masks[v]&remaining
        while neighbors:
            b=neighbors&-neighbors;neighbors^=b
            forbidden[b.bit_length()-1]|=1<<c
    return colors

def verify(n,edges,colors):
    es,masks=conflict_graph(n,edges)
    assert len(colors)==len(es)
    assert max(colors)<20
    assert all(colors[i]!=colors[j] for i,j in combinations(range(len(es)),2) if masks[i]>>j&1)

def solve(n,edges):
    es,masks=conflict_graph(n,edges)
    colors=greedy_color(masks)
    greedy=max(colors)+1
    if greedy<=20:return dict(status='sat',greedy_colors=greedy,coloring=colors)
    result=exact_color(masks,20,limit=5)
    return dict(status=result['status'],greedy_colors=greedy,coloring=result['coloring'],
                exact_visits=result['visits'],exact_seconds=result['seconds'])

def two_block_exhaustive(blocks):
    records=[];summary=[]
    for r in [2,3]:
        inds=[i for i,b in enumerate(blocks) if b['deletion_count']==r]
        count=0;start=time.monotonic()
        for ai,i in enumerate(inds):
            for j in inds[ai:]:
                a,b=blocks[i],blocks[j]
                ports_a=[v for e in a['deleted_edges'] for v in e]
                ports_b=[10+v for e in b['deleted_edges'] for v in e]
                base={tuple(e) for e in a['surviving_edges']}|{(10+u,10+v) for u,v in b['surviving_edges']}
                reconnections=set()
                for p in set(permutations(ports_b)):
                    cross=tuple(sorted(zip(ports_a,p)))
                    if len(set(cross))==2*r:reconnections.add(cross)
                for cross in sorted(reconnections):
                    edges=base|set(cross)
                    result=solve(20,edges)
                    record=dict(block_indices=[i,j],connections=cross,**result)
                    records.append(record);count+=1
                    if result['status']!='sat':
                        print('UNRESOLVED',record,flush=True)
                    else:verify(20,edges,result['coloring'])
        stats=dict(deletion_count=r,block_pair_types=len(inds)*(len(inds)+1)//2,
                   graphs=count,seconds=round(time.monotonic()-start,3),
                   greedy_histogram={str(k):sum(x['greedy_colors']==k for x in records if blocks[x['block_indices'][0]]['deletion_count']==r)
                                     for k in sorted({x['greedy_colors'] for x in records if blocks[x['block_indices'][0]]['deletion_count']==r})})
        summary.append(stats);print(stats,flush=True)
    return dict(summary=summary,records=records)

def random_gluings(blocks,trials=500,seed=290317):
    rng=random.Random(seed);results=[];attempts=0
    while len(results)<trials and attempts<trials*100:
        attempts+=1
        nblocks=rng.choice([3,4,5,6,8])
        chosen=[rng.randrange(len(blocks)) for _ in range(nblocks)]
        ports=[10*i+v for i,b in enumerate(chosen) for e in blocks[b]['deleted_edges'] for v in e]
        rng.shuffle(ports)
        cross=[tuple(sorted(ports[i:i+2])) for i in range(0,len(ports),2)]
        if any(u//10==v//10 for u,v in cross) or len(set(cross))!=len(cross):continue
        edges={(10*i+u,10*i+v) for i,b in enumerate(chosen) for u,v in blocks[b]['surviving_edges']}|set(cross)
        result=solve(10*nblocks,edges)
        if result['status']=='sat':verify(10*nblocks,edges,result['coloring'])
        results.append(dict(block_indices=chosen,connections=cross,**result))
    return dict(seed=seed,attempts=attempts,trials=len(results),records=results)

if __name__=='__main__':
    blocks=json.loads(Path('research/gadget_block_signatures.json').read_text())
    exhaustive=two_block_exhaustive(blocks)
    Path('research/gadget_two_block_gluings.json').write_text(json.dumps(exhaustive,separators=(',',':')))
    print('exhaustive_saved',len(exhaustive['records']),flush=True)
    randoms=random_gluings(blocks)
    Path('research/gadget_random_gluings.json').write_text(json.dumps(randoms,separators=(',',':')))
    print('random_trials',randoms['trials'],'statuses',
          {s:sum(x['status']==s for x in randoms['records']) for s in sorted({x['status'] for x in randoms['records']})},
          'greedy_max',max(x['greedy_colors'] for x in randoms['records']),flush=True)
