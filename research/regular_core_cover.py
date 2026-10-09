"""Frozen strong 20-coloring of a 4-regular graph of girth at least five.

Verification uses the original endpoint definition. No dependencies.
"""
import json
from pathlib import Path


def vertex(i, s, t):
    return (i % 5) * 8 + s * 4 + (t % 4)


def main():
    voltage = ((0, 0), (1, 3))
    edges, colors = [], []
    for i in range(5):
        for s in range(2):
            for z in range(2):
                for t in range(4):
                    edges.append((vertex(i, s, t),
                                  vertex(i + 1, z, t + voltage[s][z])))
                    colors.append(4 * i + 2 * s + z)
    adj = [set() for _ in range(40)]
    for u, v in edges:
        assert u != v and v not in adj[u]
        adj[u].add(v)
        adj[v].add(u)
    assert all(len(x) == 4 for x in adj)
    assert all(not (adj[u] & adj[v]) for u, v in edges)
    assert all(len(adj[u] & adj[v]) <= 1
               for u in range(40) for v in range(u + 1, 40))
    reached = {0}
    queue = [0]
    for u in queue:
        for v in adj[u] - reached:
            reached.add(v)
            queue.append(v)
    assert len(reached) == 40
    conflict = [set() for _ in edges]
    for i, e in enumerate(edges):
        for j in range(i):
            f = edges[j]
            if set(e) & set(f) or any(y in adj[x] for x in e for y in f):
                assert colors[i] != colors[j]
                conflict[i].add(j)
                conflict[j].add(i)
    assert all(len(n) == 24 for n in conflict)
    assert all({colors[j] for j in n} == set(range(20)) - {colors[i]}
               for i, n in enumerate(conflict))
    result = {
        "vertices": 40, "edges": edges, "colors": colors,
        "degree": 4, "girth_at_least": 5,
        "conflict_degree": 24, "visible_other_colors": 19,
        "connected": True,
    }
    destination = Path(__file__).with_suffix('.json')
    destination.write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('edges', 'colors')}))


if __name__ == '__main__':
    main()
