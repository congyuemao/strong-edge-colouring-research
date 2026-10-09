"""Explicit abstract two-representative obstruction, not a G/F realization.

Check graph properties and independently check all vertex-deletion colorings.
No external solver or library is required.
"""
from itertools import combinations
from pathlib import Path
import json


def build():
    # 0=p,1=q,2=a,3=b,4=c; U=5..8, V=9..12.
    edges = set(combinations(range(5), 2)) - {(0, 1), (2, 3)}
    edges |= set(combinations(range(5, 9), 2))
    edges |= set(combinations(range(9, 13), 2))
    edges |= {(0, 5), (0, 6), (1, 7), (1, 8)}
    edges |= {(2, 9), (2, 10), (3, 11), (3, 12)}
    adj = [set() for _ in range(13)]
    for x, y in edges:
        adj[x].add(y)
        adj[y].add(x)
    return edges, adj


def color(adj, removed=frozenset(), k=4):
    colors = [-1] * len(adj)
    remaining = set(range(len(adj))) - set(removed)
    nodes = 0

    def visit():
        nonlocal nodes
        nodes += 1
        if not remaining:
            return colors[:]
        v = max(remaining, key=lambda v: (len({colors[x] for x in adj[v] if colors[x] >= 0}),
                                         len(adj[v] & remaining), -v))
        forbidden = {colors[x] for x in adj[v] if colors[x] >= 0}
        remaining.remove(v)
        maximum_used = max(colors)
        for c in range(min(k, maximum_used + 2)):
            if c not in forbidden:
                colors[v] = c
                answer = visit()
                if answer is not None:
                    return answer
        colors[v] = -1
        remaining.add(v)
        return None

    return visit(), nodes


def main():
    edges, adj = build()
    is_clique = lambda vs: all(y in adj[x] for x, y in combinations(vs, 2))
    k4 = [list(s) for s in combinations(range(13), 4) if is_clique(s)]
    assert not any(is_clique(s) for s in combinations(range(13), 5))
    assert not any(len(set(s) & set(t)) == 3 for s, t in combinations(k4, 2))
    full, nodes = color(adj)
    assert full is None
    deletions = []
    for v in range(13):
        colors, count = color(adj, {v})
        assert colors is not None
        assert all(colors[x] != colors[y] for x, y in edges if v not in (x, y))
        assert all(0 <= colors[x] < 4 for x in range(13) if x != v)
        deletions.append({'deleted': v, 'colors': colors, 'search_nodes': count})
    reps = {0, 1}
    old_degree = {x: len(adj[x] - reps) for x in range(13) if x not in reps}
    saturated = {str(v): sorted(x for x in adj[v] if old_degree[x] == 4) for v in reps}
    assert max(old_degree.values()) <= 4
    assert saturated == {'0': [], '1': []}
    out = {'scope': 'Abstract graph only; no original G/F realization or global-potential certificate.',
           'labels': ['p', 'q', 'a', 'b', 'c'] + [f'u{i}' for i in range(4)] + [f'v{i}' for i in range(4)],
           'edges': sorted(edges), 'degree': [len(row) for row in adj], 'K4s': k4,
           'four_colorable': False, 'full_search_nodes': nodes,
           'deletion_certificates': deletions, 'representatives': [0, 1],
           'old_degrees': old_degree, 'saturated_sets': saturated,
           'common_old_degree_three': [2, 3], 'common_old_degree_two': [4]}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
    print(json.dumps({k: v for k, v in out.items() if k not in {'edges', 'deletion_certificates', 'labels'}}))


if __name__ == '__main__':
    main()
