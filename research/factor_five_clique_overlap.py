"""Raw endpoint checks of five-clique overlap and a unique-neighbor example.

No previous graph generation or conflict routines are imported.
"""
from itertools import combinations
from collections import Counter
from pathlib import Path
import json


def audit_graph(vertices, edges, f):
    assert len(set(edges)) == len(edges)
    adj = {x: set() for x in vertices}
    red = {x: set() for x in vertices}
    for u, v in edges:
        assert u != v
        adj[u].add(v)
        adj[v].add(u)
    for u, v in f:
        assert (u, v) in edges
        red[u].add(v)
        red[v].add(u)
    assert all(len(adj[x]) == 4 and len(red[x]) == 2 for x in vertices)
    assert all(not (adj[u] & adj[v]) for u, v in edges)
    assert all(len(adj[u] & adj[v]) <= 1 for u, v in combinations(vertices, 2))
    h = [set() for e in f]
    for i, j in combinations(range(len(f)), 2):
        e, g = f[i], f[j]
        if set(e) & set(g) or any(y in adj[x] for x in e for y in g):
            h[i].add(j)
            h[j].add(i)
    return h


def unique_neighbor():
    vertices = [(h, t, i) for h in range(3) for t in range(2) for i in range(5)]
    f, blue = [], []
    for h in range(3):
        for i in range(5):
            f += [((h, 0, i), (h, 1, i)),
                  ((h, 0, i), ((h+1) % 3, 1, i))]
            blue += [((h, 0, i), (h, 0, (i+1) % 5)),
                     ((h, 1, i), (h, 1, (i+2) % 5))]
    h = audit_graph(vertices, f + blue, f)
    q = {2*i for i in range(5)}
    assert all(j in h[i] for i, j in combinations(q, 2))
    singleton = {10+2*i: sorted(h[10+2*i] & q) for i in range(5)}
    assert all(singleton[10+2*i] == [2*i] for i in range(5))
    return {'vertices': vertices, 'F': f, 'other_edges': blue,
            'Q_indices': sorted(q), 'unique_neighbors': singleton,
            'checks': '4-regular, F 2-factor, girth >=5, Q strong, unique neighbors'}


def tower(m):
    vertices = [(k, i) for k in range(m) for i in range(5)]
    f = [((k, i), (k, (i+1) % 5)) for k, i in vertices]
    blue = [((k, i), ((k+1) % m, 2*i % 5)) for k, i in vertices]
    h = audit_graph(vertices, f + blue, f)
    cliques = set()
    for k in range(m):
        layer = set(range(5*k, 5*k+5))
        next_layer = set(range(5*((k+1) % m), 5*((k+1) % m)+5))
        local = []
        for q in combinations(sorted(layer | next_layer), 5):
            if all(j in h[i] for i, j in combinations(q, 2)):
                local.append(q)
                cliques.add(q)
        assert len(local) == 32
    assert len(cliques) == 31*m
    cliques = sorted(cliques)
    four_to_cliques = {}
    for i, q in enumerate(cliques):
        for four in combinations(q, 4):
            four_to_cliques.setdefault(four, []).append(i)
    overlap = [set() for _ in cliques]
    for containing in four_to_cliques.values():
        assert len(containing) <= 3
        for i, j in combinations(containing, 2):
            overlap[i].add(j)
            overlap[j].add(i)
    seen, queue = {0}, [0]
    for i in queue:
        for j in overlap[i] - seen:
            seen.add(j)
            queue.append(j)
    assert len(seen) == len(cliques)
    assert sum(map(len, overlap)) // 2 == 85*m
    degrees = Counter(map(len, overlap))
    assert degrees == {5: 20*m, 6: 10*m, 10: m}
    triangles = sum(len(overlap[i] & overlap[j]) for i in range(len(overlap))
                    for j in overlap[i] if i < j) // 3
    assert triangles == 5*m
    return {'layers': m, 'vertices': len(vertices), 'F_edges': len(f),
            'five_cliques': len(cliques), 'overlap_components': 1,
            'overlap_edges': 85*m, 'overlap_degrees': dict(degrees),
            'overlap_triangles': triangles, 'checks': 'all passed'}


def main():
    result = {'unique_neighbor_four_regular': unique_neighbor(),
              'tower_overlap': [tower(m) for m in (5, 6, 7, 11)]}
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result['tower_overlap']))
    print('Thirty-vertex unique-neighbor certificate: all assertions passed.')


if __name__ == '__main__':
    main()
