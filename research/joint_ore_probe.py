"""Finite probe: Ore compositions of two explicit O9 cores.

This is not an enumeration of all 5-critical graphs.  Test whether deleting
two independent representatives can satisfy the necessary old-degree and
saturated-neighbour clique conditions of the (4,4,2) partition.
"""
from itertools import combinations
from pathlib import Path
import json


def base():
    ed = set(combinations(range(4), 2))
    ed |= set(combinations((0, 1, 4, 5), 2))
    ed |= set(combinations((2, 3, 6, 7), 2))
    ed |= {(4, 8), (5, 8), (6, 8), (7, 8)}
    adj = [set() for _ in range(9)]
    for u, v in ed:
        adj[u].add(v)
        adj[v].add(u)
    return ed, adj


def ore(edge, split_vertex, half):
    ed, adj = base()
    u, v = edge
    right = {x: 9 + i for i, x in enumerate(x for x in range(9) if x != split_vertex)}
    out = ed - {tuple(sorted(edge))}
    out |= {tuple(sorted((right[a], right[b]))) for a, b in ed
            if split_vertex not in (a, b)}
    out |= {tuple(sorted((u if x in half else v, right[x]))) for x in adj[split_vertex]}
    return out


def clique(adj, vertices):
    return all(v in adj[u] for u, v in combinations(vertices, 2))


def inspect(ed):
    n = 17
    adj = [set() for _ in range(n)]
    for u, v in ed:
        adj[u].add(v)
        adj[v].add(u)
    assert all(4 <= len(row) <= 5 for row in adj)
    k4 = [set(t) for t in combinations(range(n), 4) if clique(adj, t)]
    if any(clique(adj, t) for t in combinations(range(n), 5)):
        return 'contains_K5', []
    if any(len(x & y) == 3 for x, y in combinations(k4, 2)):
        return 'K4_overlap_three', []
    degree_pairs = []
    accepted = []
    for p, q in combinations(range(n), 2):
        if q in adj[p]:
            continue
        chosen = {p, q}
        old_degree = {v: len(adj[v] - chosen) for v in range(n) if v not in chosen}
        if max(old_degree.values()) > 4:
            continue
        degree_pairs.append([p, q])
        sets = [[v for v in adj[t] if v not in chosen and old_degree[v] == 4]
                for t in (p, q)]
        if all(len(s) <= 3 and clique(adj, s) for s in sets):
            accepted.append({'pair': [p, q], 'saturated_sets': sets,
                             'critical_degrees': [len(adj[p]), len(adj[q])]})
    return 'passes_clique_geometry', {'old_degree_pairs': degree_pairs,
                                     'accepted_pairs': accepted}


def main():
    ed, adj = base()
    lows = [v for v in range(9) if len(adj[v]) == 4]
    low_edges = sorted((u, v) for u, v in ed if u in lows and v in lows)
    rows = []
    for edge in low_edges:
        for split in lows:
            ns = sorted(adj[split])
            # Both attachments to the ordered left edge endpoints matter.
            # All six halves include both directions of each unordered split.
            for pair in combinations(ns, 2):
                half = set(pair)
                joined = ore(edge, split, half)
                status, result = inspect(joined)
                rows.append({'edge': edge, 'split': split, 'half': sorted(half),
                             'status': status, 'result': result,
                             'edges': sorted(joined)})
    assert len(rows) == 180
    survivors = [r for r in rows if isinstance(r['result'], dict)
                 and r['result']['accepted_pairs']]
    out = {'scope': 'Only these 180 labelled Ore compositions, with both attachment directions; not all critical graphs.',
           'base_edges': sorted(ed), 'graphs': len(rows),
           'clique_geometry_pass': sum(r['status'] == 'passes_clique_geometry' for r in rows),
           'pair_condition_survivors': len(survivors), 'rows': rows}
    path = Path(__file__).with_suffix('.json')
    path.write_text(json.dumps(out, indent=2), encoding='utf-8')
    print(json.dumps({k: v for k, v in out.items() if k != 'rows'}))


if __name__ == '__main__':
    main()
