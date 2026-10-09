"""Independent verification of the infinite periodic obstruction and real boundaries."""
from itertools import combinations
from collections import deque
from pathlib import Path
import json

def verify_automaton(name):
    data=json.loads(Path('research/'+name).read_text())
    pattern=data['pattern'];period=len(pattern)
    states=[(i,tuple(s)) for i,s in data['states']]
    index={s:i for i,s in enumerate(states)}
    assert len(index)==len(states)
    pairs=[{sum(1<<c for c in p) for p in combinations([c for c in range(8) if L>>c&1],2)} for L in pattern]
    expected=set()
    for phase in range(period):
        for s in pairs[phase]:
            for t in pairs[(phase+1)%period]:
                if s&t:continue
                for a,b in ((a,b) for a in range(8) for b in range(8) if a!=b):
                    if not (s|t)&((1<<a)|(1<<b)):expected.add((phase,(s,t,a,b)))
    assert set(states)==expected
    order=data['deletion_order'];assert sorted(order)==list(range(len(states)))
    rank={v:i for i,v in enumerate(order)}
    for v,(phase,(s,t,a,b)) in enumerate(states):
        expected_neighbors=set()
        for u in pairs[(phase+2)%period]:
            if u&t or u>>b&1:continue
            for c in range(8):
                if c not in (a,b) and not (s|t|u)>>c&1:
                    expected_neighbors.add(index[((phase+1)%period,(t,u,b,c))])
        assert set(data['adjacency'][v])==expected_neighbors
        assert all(rank[w]<rank[v] for w in expected_neighbors)
    print('DAG certificate verified: period',period,'states',len(states),'arcs',sum(map(len,data['adjacency'])))

def verify_boundaries():
    certificates=json.loads(Path('research/high_girth_real_boundary_certificates.json').read_text())
    for data in certificates:
        edges=[tuple(e) for e in data['edges']];n=data['vertices'];adj=[set() for _ in range(n)]
        partial=data['initial_partial_coloring'];full=data['full_11_coloring']
        for u,v in edges:adj[u].add(v);adj[v].add(u)
        assert max(map(len,adj))<=4 and len(edges)==n
        seen={0};queue=deque([0])
        while queue:
            v=queue.popleft()
            for w in adj[v]-seen:seen.add(w);queue.append(w)
        assert len(seen)==n
        degree=list(map(len,adj));queue=deque(v for v,d in enumerate(degree) if d==1)
        while queue:
            v=queue.popleft();degree[v]=0
            for w in adj[v]:
                if degree[w]:
                    degree[w]-=1
                    if degree[w]==1:queue.append(w)
        assert sum(d>0 for d in degree)==data['cycle_length']
        assert all(d in (0,2) for d in degree)
        conflicts=[set() for _ in edges]
        for i,j in combinations(range(len(edges)),2):
            e,f=edges[i],edges[j]
            if set(e)&set(f) or any(w in adj[v] for v in e for w in f):
                conflicts[i].add(j);conflicts[j].add(i)
                assert full[i]!=full[j]
                if partial[i]>=0 and partial[j]>=0:assert partial[i]!=partial[j]
        assert max(full)<11 and max(partial)<20
        edge_index={e:i for i,e in enumerate(edges)}
        for edge,wanted in zip(data['core_edges'],data['core_lists']):
            i=edge_index[tuple(edge)];used={partial[j] for j in conflicts[i] if partial[j]>=0}
            actual=sum(1<<c for c in range(20) if c not in used)
            assert actual==wanted
        print('Real boundary verified: girth',data['cycle_length'],'vertices',n,'partial 20 colors; full <=11 colors')

if __name__=='__main__':
    verify_automaton('high_girth_12_periodic_dag.json')
    verify_boundaries()
