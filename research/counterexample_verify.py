"""Direct reproducible verification of the two explicit constructions."""
from itertools import combinations

def adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for u,v in edges:
        assert u != v and v not in adj[u]
        adj[u].add(v)
        adj[v].add(u)
    return adj

def conflict(e, f, adj):
    return bool(set(e) & set(f)) or any(y in adj[x] for x in e for y in f)

def lower_bound():
    edges = [tuple(sorted((2*i+j,2*((i+1)%5)+k)))
             for i in range(5) for j in range(2) for k in range(2)]
    adj = adjacency(10, edges)
    assert len(edges) == 20
    assert all(len(a)==4 for a in adj)
    assert all(conflict(e,f,adj) for e,f in combinations(edges,2))
    return dict(vertices=10, edges=20, degree=4, conflict_pairs=190,
                exact_required_colors=20)

def local_obstruction():
    xs = [list(range(5+3*i,8+3*i)) for i in range(4)]
    branches = [(1+i,x) for i in range(4) for x in xs[i]]
    edges = [(0,1+i) for i in range(4)] + branches
    edges += [(x,y) for i,j in [(0,1),(2,3)] for x in xs[i] for y in xs[j]]
    adj = adjacency(17, edges)
    assert len(edges)==34 and all(len(a)==4 for a in adj)
    assert all(not (adj[u] & adj[v]) for u,v in edges)
    assert all(not ((adj[u] & adj[v])-{0}) for u,v in combinations(adj[0],2))
    assert not any(all(not conflict(e,f,adj) for e,f in combinations(triple,2))
                   for triple in combinations(branches,3))
    assert any(not conflict(e,f,adj) for e,f in combinations(branches,2))
    return dict(vertices=17, edges=34, degree=4, triangles=0,
                four_cycles_through_root=0, branch_induced_matching_number=2)

if __name__ == '__main__':
    print('20-color lower bound:', lower_bound())
    print('Local lemma obstruction:', local_obstruction())
