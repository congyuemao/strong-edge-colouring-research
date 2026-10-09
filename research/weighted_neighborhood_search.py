"""Targeted check of the squared-weight neighborhood-coloring criterion.

Only an obstruction is conclusive globally. Negative finite searches are
reported only for the specified C5-blowup deletion family.
"""
from research.gadget_blocks import BASE, deletion_orbits, maximum_clique
from research.high_conflict_cliques import adjacency,conflict,pad_neighborhoods
from pathlib import Path
import json


def search():
    records=[]
    for r in range(5):
        for rep,size in deletion_orbits(r):
            es=[e for i,e in enumerate(BASE) if i not in rep]
            adj=adjacency(10,es)
            masks=[sum(1<<j for j,f in enumerate(es) if i!=j and conflict(e,f,adj))
                   for i,e in enumerate(es)]
            for i,(u,v) in enumerate(es):
                outer=(adj[u]-{v})|(adj[v]-{u})
                degree=24-sum(a in outer and b in outer for a,b in es)
                if degree<21:
                    continue
                ns=[j for j in range(len(es)) if masks[i]>>j&1]
                sub=[sum(1<<k for k,l in enumerate(ns) if masks[j]>>l&1) for j in ns]
                q=[ns[t] for t in maximum_clique(sub)]
                if len(q)>38-degree:
                    n,full=pad_neighborhoods(10,es)
                    fulladj=adjacency(n,full)
                    actual=sum(e!=es[i] and conflict(es[i],e,fulladj) for e in full)
                    assert actual==degree
                    result=dict(found=True,deleted=rep,root=es[i],degree=degree,
                        clique=[es[j] for j in q],base=es,vertex_count=n,edges=full)
                    Path('research/weighted_neighborhood_search.json').write_text(json.dumps(result,indent=2))
                    return result
        records.append(dict(deletions=r,orbits=len(deletion_orbits(r))))
        print('done',r,flush=True)
    result=dict(found=False,checked=records)
    Path('research/weighted_neighborhood_search.json').write_text(json.dumps(result,indent=2))
    return result


if __name__=='__main__':
    print(json.dumps(search()))
