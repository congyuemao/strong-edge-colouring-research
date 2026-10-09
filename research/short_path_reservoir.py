"""Exact induced-matching test of the saved 40-vertex high-girth graph.

Independent endpoint conflict construction; no third-party packages.
The branch search upper bound is a greedy proper coloring of the candidate
compatibility graph, not a heuristic bound on the maximum clique.
"""
import json
from pathlib import Path
from time import perf_counter


def maximum_clique(adj):
    best, calls = [], 0

    def color_order(candidates):
        order, bounds = [], []
        color = 0
        while candidates:
            color += 1
            available = candidates
            while available:
                bit = available & -available
                v = bit.bit_length() - 1
                order.append(v)
                bounds.append(color)
                candidates ^= bit
                available ^= bit
                available &= ~adj[v]
        return order, bounds

    def visit(chosen, candidates):
        nonlocal best, calls
        calls += 1
        order, bounds = color_order(candidates)
        for i in range(len(order) - 1, -1, -1):
            if len(chosen) + bounds[i] <= len(best):
                return
            v = order[i]
            rem = candidates & adj[v]
            if rem:
                visit(chosen + [v], rem)
            elif len(chosen) + 1 > len(best):
                best = chosen + [v]
            candidates &= ~(1 << v)

    visit([], (1 << len(adj)) - 1)
    return best, calls


def main():
    start = perf_counter()
    source = Path(__file__).with_name('regular_core_cover.json')
    data = json.loads(source.read_text(encoding='utf-8'))
    edges, n = data['edges'], data['vertices']
    adjacency = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v and v not in adjacency[u]
        adjacency[u].add(v)
        adjacency[v].add(u)
    assert all(len(a) == 4 for a in adjacency)
    assert all(not (adjacency[u] & adjacency[v]) for u, v in edges)
    assert all(len(adjacency[u] & adjacency[v]) <= 1
               for u in range(n) for v in range(u))
    compatible = [0] * len(edges)
    for i, (u, v) in enumerate(edges):
        for j, (x, y) in enumerate(edges[:i]):
            conflict = (len({u, v, x, y}) < 4
                        or x in adjacency[u] or y in adjacency[u]
                        or x in adjacency[v] or y in adjacency[v])
            if not conflict:
                compatible[i] |= 1 << j
                compatible[j] |= 1 << i
    witness, calls = maximum_clique(compatible)
    assert all(compatible[u] & (1 << v)
               for u in witness for v in witness if u != v)
    result = {
        'vertices': n, 'edges': len(edges),
        'maximum_induced_matching': len(witness),
        'witness_edge_indices': witness,
        'witness_edges': [edges[i] for i in witness],
        'search_calls': calls,
        'elapsed_seconds': perf_counter() - start,
        'two_colors_maximum_size_upper_bound': 2 * len(witness),
        'two_paths_lengths_2_and_4_required_reservoir':
            (8 * n + 14) // 15,
    }
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
