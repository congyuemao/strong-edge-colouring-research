"""Exhaustive 2/3-edge-deletion orbits and unlabeled coloring partitions.

The base graph and all automorphisms are explicitly constructed here.
No external packages or graph catalogues are used.
"""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import json
from research.counterexample_splice import tight_edges, conflict_graph

BASE=sorted(tight_edges())
INDEX={e:i for i,e in enumerate(BASE)}

def edge_automorphisms():
    result=[]
    for sign in [1,-1]:
        for rotation in range(5):
            for flips in range(32):
                vertex_map=[2*((sign*(v//2)+rotation)%5)+(v%2 ^ (flips>>(v//2)&1)) for v in range(10)]
                edge_map=tuple(INDEX[tuple(sorted((vertex_map[u],vertex_map[v])))] for u,v in BASE)
                result.append(edge_map)
    assert len(set(result))==320
    return result

AUTOS=edge_automorphisms()

def deletion_orbits(r):
    unseen=set(combinations(range(20),r))
    answer=[]
    while unseen:
        representative=min(unseen)
        orbit={tuple(sorted(p[e] for e in representative)) for p in AUTOS}
        assert orbit <= unseen
        unseen-=orbit
        answer.append((representative,len(orbit)))
    return answer

def coloring_partitions(masks):
    """Count every proper coloring modulo permutation of color names.

    Every partition has a unique class containing its least remaining
    edge. Enumerating all independent sets containing that edge therefore
    counts every partition exactly once.
    """
    n=len(masks);allmask=(1<<n)-1
    compat=[allmask&~masks[v]&~(1<<v) for v in range(n)]
    def independent_extensions(chosen,candidates):
        yield chosen
        while candidates:
            b=candidates&-candidates;candidates^=b
            w=b.bit_length()-1
            yield from independent_extensions(chosen|b,candidates&compat[w])
    @lru_cache(None)
    def count(remaining):
        if not remaining:return (1,)
        b=remaining&-remaining;v=b.bit_length()-1
        histogram=[0]*(remaining.bit_count()+1)
        for color_class in independent_extensions(b,remaining&compat[v]):
            sub=count(remaining^color_class)
            for k,c in enumerate(sub):histogram[k+1]+=c
        return tuple(histogram)
    histogram=count(allmask)
    chi=next(i for i,c in enumerate(histogram) if c)
    coloring=[-1]*n
    remaining=allmask;k=chi;c=0
    while remaining:
        b=remaining&-remaining;v=b.bit_length()-1
        for color_class in independent_extensions(b,remaining&compat[v]):
            sub=count(remaining^color_class)
            if k-1<len(sub) and sub[k-1]:break
        for v in range(n):
            if color_class>>v&1:coloring[v]=c
        remaining^=color_class;k-=1;c+=1
    assert all(coloring[i]!=coloring[j] for i,j in combinations(range(n),2) if masks[i]>>j&1)
    return dict(chromatic_number=chi,partition_histogram={str(k):c for k,c in enumerate(histogram) if c},
                total_partitions=sum(histogram),minimum_coloring=coloring,dp_states=count.cache_info().currsize)

def maximum_clique(masks):
    best=[]
    def visit(chosen,candidates):
        nonlocal best
        if len(chosen)+candidates.bit_count()<=len(best):return
        if not candidates:
            best=list(chosen);return
        while candidates:
            if len(chosen)+candidates.bit_count()<=len(best):return
            b=candidates&-candidates;candidates^=b
            v=b.bit_length()-1
            visit(chosen+[v],candidates&masks[v])
    visit([],(1<<len(masks))-1)
    assert all(masks[i]>>j&1 for i,j in combinations(best,2))
    return best

def all_partitions(masks):
    """Explicit normalized signatures, including every boundary projection."""
    n=len(masks);allmask=(1<<n)-1
    compat=[allmask&~masks[v]&~(1<<v) for v in range(n)]
    def independent_extensions(chosen,candidates):
        yield chosen
        while candidates:
            b=candidates&-candidates;candidates^=b
            yield from independent_extensions(chosen|b,candidates&compat[b.bit_length()-1])
    def partitions(remaining,classes):
        if not remaining:
            coloring=[-1]*n
            for c,part in enumerate(classes):
                for v in range(n):
                    if part>>v&1:coloring[v]=c
            yield coloring;return
        b=remaining&-remaining;v=b.bit_length()-1
        for part in independent_extensions(b,remaining&compat[v]):
            yield from partitions(remaining^part,classes+[part])
    return list(partitions(allmask,[]))

def run():
    results=[]
    for r in [2,3]:
        for rep,size in deletion_orbits(r):
            deleted=[BASE[i] for i in rep]
            edges,masks=conflict_graph(10,set(BASE)-set(deleted))
            rec=dict(deletion_count=r,deleted_edges=deleted,orbit_size=size,
                     surviving_edges=edges,ports=sorted({v for e in deleted for v in e}),
                     **coloring_partitions(masks))
            rec['maximum_clique']=maximum_clique(masks)
            rec['all_color_partitions']=all_partitions(masks)
            assert len(rec['all_color_partitions'])==rec['total_partitions']
            results.append(rec)
    return results

if __name__=='__main__':
    result=run()
    Path('research/gadget_block_signatures.json').write_text(json.dumps(result,indent=2))
    for r in [2,3]:
        block=[x for x in result if x['deletion_count']==r]
        print('deleted',r,'orbits',len(block),'labeled cuts',sum(x['orbit_size'] for x in block),
              'chromatic distribution',{k:sum(x['orbit_size'] for x in block if x['chromatic_number']==k)
                                        for k in sorted({x['chromatic_number'] for x in block})},
              'max partitions',max(x['total_partitions'] for x in block))
    for x in result:print(x['deleted_edges'],x['chromatic_number'],x['total_partitions'])
