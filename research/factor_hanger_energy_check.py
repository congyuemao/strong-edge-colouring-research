"""Independent 6-variable / three K4-block check of the 18-edge energy data.

Read raw endpoint certificates, not the search or its graph routines.
Enumerate 3^6 auxiliary assignments and exactly minimize each four-point
block by its 3^4 assignments; this is independent of branch-and-bound.
"""
from pathlib import Path
from itertools import product,combinations
import json


def check(row):
    f=[tuple(e) for e in row['F_core']];idx={e:i for i,e in enumerate(f)}
    g=[tuple(e) for e in row['structure']['G_core']]
    adj={v:set() for e in g for v in e}
    for u,v in g:adj[u].add(v);adj[v].add(u)
    h=[set() for e in f]
    for i,j in combinations(range(len(f)),2):
        e,z=f[i],f[j]
        if set(e)&set(z) or any(b in adj[a] for a in e for b in z):
            h[i].add(j);h[j].add(i)
    central=[idx[tuple(e)] for e in row['structure']['central']]
    qsets=[{idx[tuple(e)] for e in q} for q in row['structure']['Q']]
    blocks=[sorted(q-{central[i]}) for i,q in enumerate(qsets)]
    aux=sorted(set(range(len(f)))-set().union(*map(set,blocks)))
    assert len(aux)==6 and all(len(b)==4 for b in blocks)
    assert all(j in h[i] for b in blocks for i,j in combinations(b,2))
    assert all(not(h[i]&set(blocks[b])) for a in range(3) for b in range(a+1,3) for i in blocks[a])
    old=row['old_colors']
    totals=[None]*len(f)
    for k,q in enumerate(qsets):
        for i in q:
            totals[i]=([4,4,4] if k==0 else [5,3,4]) if i==central[k] else ([4,4,4] if k==0 else [3,5,4])
    for key,ds in (('L',[5,5,2]),('M',[4,2,6]),('f2',[4,7,1])):
        totals[idx[tuple(row['structure'][key])]]=ds
    outside=[[totals[i][c]-sum(old[j]==c for j in h[i]) for c in range(3)] for i in range(len(f))]
    assert outside==row['outside_counts'] and all(o[0]==0 for o in outside)
    unary=[[outside[i][c]-(4,3,3)[c] for c in range(3)] for i in range(len(f))]
    best=10**9;witnesses=[];aux_assignments=0
    for labels in product(range(3),repeat=6):
        aux_assignments+=1
        cs=dict(zip(aux,labels))
        value=sum(unary[i][cs[i]] for i in aux)+sum(cs[i]==cs[j] for i,j in combinations(aux,2) if j in h[i])
        choices=[]
        for block in blocks:
            low=10**9;opts=[]
            for xs in product(range(3),repeat=4):
                now=dict(zip(block,xs))
                v=sum(unary[i][now[i]] for i in block)
                v+=sum(now[i]==now[j] for i,j in combinations(block,2))
                v+=sum(now[i]==cs[j] for i in block for j in h[i]&set(aux))
                if v<low:low=v;opts=[xs]
                elif v==low:opts.append(xs)
            value+=low;choices.append(opts)
        if value>best:continue
        if value<best:best=value;witnesses=[]
        for block_labels in product(*choices):
            coloring=[None]*len(f)
            for i,c in cs.items():coloring[i]=c
            for block,xs in zip(blocks,block_labels):
                for i,c in zip(block,xs):coloring[i]=c
            witnesses.append(coloring)
    assert best==row['minimum_energy']==row['original_energy']
    assert len(witnesses)==3
    expected=[]
    for k in range(3):
        coloring=old[:]
        for j,i in enumerate(central):coloring[i]=0 if j==k else 1
        expected.append(coloring)
    assert {tuple(c) for c in witnesses}=={tuple(c) for c in expected}
    return {'types':row['types'],'nuclear_choice':row['nuclear_choice'],
            'minimum':best,'aux_assignments':aux_assignments,
            'minimum_states':3,'states_exactly_central_swaps':True,
            'all_outside_A_counts_zero':True}


def main():
    rows=json.loads(Path(__file__).with_name('factor_hanger_energy.json').read_text(encoding='utf-8'))
    out=[check(row) for row in rows]
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
    print(json.dumps(out))


if __name__=='__main__':main()
