"""Realize even-cycle bad lists by an actual exterior 20-coloring.

Also construct and verify an 11-color recoloring of the entire graph.
"""
from pathlib import Path
from itertools import combinations
import json

def construct(pattern):
    n=len(pattern)
    assert n>=6 and n%2==0
    edges=[];partial={};full={};next_vertex=n
    cycle=[];spokes=[]
    for i in range(n):
        e=tuple(sorted((i,(i+1)%n)));edges.append(e);cycle.append(e)
    for i in range(n):
        six=list(range(8,14)) if i%2==0 else list(range(14,20))
        opposite=list(range(14,20)) if i%2==0 else list(range(8,14))
        missing=[c for c in range(8) if not pattern[i]>>c&1]
        root_colors=[0,1] if i%2==0 else [2,3]
        e_colors=[c for c in range(7) if c not in root_colors][:3]
        for alpha in range(2):
            u=next_vertex;next_vertex+=1
            e=(i,u);edges.append(e);spokes.append(e);full[e]=root_colors[alpha]
            d_colors=[c for c in range(7) if c not in e_colors and c!=root_colors[alpha]]
            assert len(d_colors)==3
            for j in range(3):
                w=next_vertex;next_vertex+=1
                e=(u,w);edges.append(e);partial[e]=six[3*alpha+j];full[e]=e_colors[j]
                for k in range(3):
                    z=next_vertex;next_vertex+=1
                    e=(w,z);edges.append(e);partial[e]=(opposite+missing)[3*j+k];full[e]=d_colors[k]
    for b in range(3):
        if n>=4*b and (n-4*b)%3==0:break
    a=(n-4*b)//3
    circle_colors=[7,8,9]*a+[7,8,9,10]*b
    assert len(circle_colors)==n
    full.update(zip(cycle,circle_colors))
    edges=sorted(edges)
    adjacency=[set() for _ in range(next_vertex)]
    for u,v in edges:adjacency[u].add(v);adjacency[v].add(u)
    assert len(edges)==next_vertex==27*n
    assert max(map(len,adjacency))==4
    def conflict(e,f):return bool(set(e)&set(f)) or any(y in adjacency[x] for x in e for y in f)
    for e,f in combinations(edges,2):
        if conflict(e,f):
            assert full[e]!=full[f]
            if e in partial and f in partial:assert partial[e]!=partial[f]
    lists={e:((1<<20)-1)&~sum(1<<c for c in {partial[f] for f in partial if conflict(e,f)}) for e in cycle+spokes}
    assert all(lists[e]==255 for e in cycle)
    assert all(lists[e]==pattern[i] for i in range(n) for e in spokes[2*i:2*i+2])
    return dict(cycle_length=n,vertices=next_vertex,edges=edges,
                initial_partial_coloring=[partial.get(e,-1) for e in edges],
                full_11_coloring=[full[e] for e in edges],
                core_edges=cycle+spokes,core_lists=[lists[e] for e in cycle+spokes])

if __name__=='__main__':
    patterns=json.loads(Path('research/high_girth_optimized_lists.json').read_text())
    p8=patterns[1]['groups'];p12=patterns[5]['groups']
    result=[construct(p8),construct(p12),construct(p12*2)]
    Path('research/high_girth_real_boundary_certificates.json').write_text(json.dumps(result,separators=(',',':')))
    for r in result:print('girth',r['cycle_length'],'vertices/edges',r['vertices'],'actual_20_boundary_verified; full colors',len(set(r['full_11_coloring'])))
