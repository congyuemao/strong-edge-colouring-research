"""Check the subdivided K4,4 obstruction to the uniform neighborhood bound."""
from pathlib import Path
from itertools import combinations
import json


def run():
    # u=0, v=1, a_1..a_3=2..4, b_1..b_4=5..8.
    core=[(a,b) for a in range(2,5) for b in range(5,9)]
    core += [(0,b) for b in range(5,8)] + [(1,8),(0,1)]
    # c_1=9,c_2=10; each has three leaves.
    edges=core+[(1,9),(1,10)]+[(9,11),(9,12),(9,13),(10,14),(10,15),(10,16)]
    adjacency=[set() for _ in range(17)]
    for u,v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    def conflict(e,f):
        return bool(set(e)&set(f)) or any(y in adjacency[x] for x in e for y in f)
    assert len(edges)==25 and max(map(len,adjacency))==4
    assert all(conflict(e,f) for e,f in combinations(core,2))
    root=(0,1)
    degree=sum(e!=root and conflict(e,root) for e in edges)
    assert degree==24
    colors=list(range(17))
    lookup={e:i for i,e in enumerate(core)}
    colors += [lookup[(2,5)],lookup[(2,6)]]
    colors += [lookup[(0,b)] for b in range(5,8)]*2
    assert all(colors[i]!=colors[j] for i,j in combinations(range(25),2)
               if conflict(edges[i],edges[j]))
    record=dict(vertex_count=17,edge_count=25,edges=edges,strong_clique=core,
                root=root,root_conflict_degree=degree,coloring=colors,
                chromatic_number=17,root_neighborhood_chromatic_number=16)
    Path('research/weighted_neighborhood_counterexample.json').write_text(json.dumps(record,indent=2))
    return {k:record[k] for k in ['vertex_count','edge_count','root','root_conflict_degree',
                                'chromatic_number','root_neighborhood_chromatic_number']}


if __name__=='__main__':
    print(json.dumps(run()))
