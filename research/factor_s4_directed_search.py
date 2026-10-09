"""Directed S4-cover experiment; all claims are finite computational results.

Search starts at the hardest saved cyclic covers and visits admissible single-
edge permutation changes. Exact independence number guides the frontier.
Every reported upper bound includes a raw-endpoint verified color certificate.
"""
from collections import Counter
from itertools import combinations, permutations
import heapq
import json
from pathlib import Path
from factor_cover_independent_audit import BASE, PATHS, inverse
from short_path_reservoir import maximum_clique
from counterexample_splice import exact_color

ROOT = Path(__file__).resolve().parent
P = list(permutations(range(4)))
PINDEX = {p: i for i, p in enumerate(P)}
PINV = [inverse(p) for p in P]
ID = PINDEX[(0, 1, 2, 3)]
CHECKS = [[] for _ in range(12)]
for path in PATHS:
    for j, _ in path:
        if j >= 10:
            CHECKS[j - 10].append(path)


def legal_paths(state, paths):
    for path in paths:
        for x in range(4):
            y = x
            for j, forward in path:
                if j >= 10:
                    t = state[j - 10]
                    y = (P[t] if forward else PINV[t])[y]
            if x == y:
                return False
    return True


def build(state):
    edges = []
    factor = []
    adj = [set() for _ in range(44)]
    for j, (u, v) in enumerate(BASE):
        perm = P[ID if j < 10 else state[j - 10]]
        for x, y in enumerate(perm):
            a, b = 4 * u + x, 4 * v + y
            edges.append((a, b))
            adj[a].add(b)
            adj[b].add(a)
            if j < 11:
                factor.append((a, b))
    assert all(len(ns) == 4 for ns in adj)
    assert all(not adj[a] & adj[b] for a, b in edges)
    assert all(len(adj[a] & adj[b]) <= 1 for a in range(44) for b in range(a))
    assert Counter(v for e in factor for v in e) == Counter({v: 2 for v in range(44)})
    masks = [0] * 44
    for i, (a, b) in enumerate(factor):
        for j, (c, d) in enumerate(factor[:i]):
            if (len({a, b, c, d}) < 4 or c in adj[a] or d in adj[a]
                    or c in adj[b] or d in adj[b]):
                masks[i] |= 1 << j
                masks[j] |= 1 << i
    assert all(m.bit_count() == 12 for m in masks)
    return edges, factor, masks


def greedy(masks, reverse=False):
    colors = [-1] * 44
    remaining = set(range(44))
    while remaining:
        v = max(remaining, key=lambda v: (
            len({colors[u] for u in range(44) if masks[v] >> u & 1 and colors[u] >= 0}),
            (masks[v] & sum(1 << u for u in remaining)).bit_count(),
            -v if reverse else v))
        forbidden = {colors[u] for u in range(44) if masks[v] >> u & 1}
        colors[v] = next(c for c in range(44) if c not in forbidden)
        remaining.remove(v)
    return colors


def group_size(state):
    group = {P[ID]}
    todo = [P[ID]]
    generators = [P[i] for i in set(state)]
    while todo:
        a = todo.pop()
        for b in generators:
            c = tuple(a[b[x]] for x in range(4))
            if c not in group:
                group.add(c)
                todo.append(c)
    return len(group)


def verify_colors(edges, factor, colors):
    assert len(colors) == 44
    es = {frozenset(e) for e in edges}
    for i, e in enumerate(factor):
        for j, f in enumerate(factor[:i]):
            if colors[i] == colors[j]:
                assert not set(e) & set(f)
                assert not any(frozenset((a, b)) in es for a in e for b in f)


def main():
    source = json.loads((ROOT / 'factor_cyclic_lift_4.json').read_text(encoding='utf-8'))
    seeds = sorted(source['certificates'], key=lambda r: -r['number_of_colors'])[:15]
    visited = {}
    queue = []
    serial = 0
    independent_calls = 0

    def assess(state, parent=None):
        nonlocal serial, independent_calls
        if state in visited:
            return
        assert legal_paths(state, PATHS)
        edges, factor, masks = build(state)
        colorings = [greedy(masks), greedy(masks, True)]
        colors = min(colorings, key=lambda c: max(c))
        verify_colors(edges, factor, colors)
        compatible = [((1 << 44) - 1) & ~(m | (1 << v)) for v, m in enumerate(masks)]
        independent, calls = maximum_clique(compatible)
        independent_calls += calls
        alpha = len(independent)
        assert all(not (masks[a] >> b & 1) for a, b in combinations(independent, 2))
        row = {'permutation_indices': list(state), 'permutations': [list(P[i]) for i in state],
               'group_size': group_size(state), 'alpha': alpha,
               'independent_witness': independent, 'alpha_search_calls': calls,
               'coloring': colors, 'color_count': max(colors) + 1,
               'parent': list(parent) if parent is not None else None}
        visited[state] = row
        heapq.heappush(queue, (alpha, -(max(colors) + 1), serial, state))
        serial += 1

    for seed in seeds:
        state = tuple(PINDEX[tuple((x + b) % 4 for x in range(4))] for b in seed['voltages'])
        assess(state)
    expanded = 0
    legal_mutations = 0
    budget = 450
    while queue and len(visited) < budget and expanded < 40:
        _, _, _, state = heapq.heappop(queue)
        expanded += 1
        for j in range(12):
            for pi in range(24):
                if pi == state[j]:
                    continue
                child = state[:j] + (pi,) + state[j + 1:]
                if child in visited or not legal_paths(child, CHECKS[j]):
                    continue
                legal_mutations += 1
                assess(child, state)
                if len(visited) >= budget:
                    break
            if len(visited) >= budget:
                break
        if expanded % 5 == 0:
            print('expanded', expanded, 'assessed', len(visited), flush=True)
    hard = sorted(visited.values(), key=lambda r: (r['alpha'], -r['color_count'], -r['group_size']))[:6]
    exact_records = []
    for row in hard:
        state = tuple(row['permutation_indices'])
        edges, factor, masks = build(state)
        lower = (44 + row['alpha'] - 1) // row['alpha']
        upper = row['color_count']
        trials = []
        for k in range(lower, upper):
            result = exact_color(masks, k, limit=8.0)
            trials.append(result)
            print('exact', k, result['status'], result['visits'], flush=True)
            if result['status'] == 'sat':
                verify_colors(edges, factor, result['coloring'])
                row['coloring'] = result['coloring']
                row['color_count'] = k
                break
            if result['status'] == 'timeout':
                break
        exact_records.append({'permutation_indices': row['permutation_indices'],
                              'trials': trials})
    result = {'description': 'Directed admissible S4 mutations; not exhaustive S4 coverage',
              'base_edges': BASE, 'fiber_size': 4, 'permutation_table': P,
              'expanded_frontier_states': expanded, 'assessed_states': len(visited),
              'new_legal_mutations': legal_mutations,
              'group_size_distribution': dict(sorted(Counter(r['group_size'] for r in visited.values()).items())),
              'alpha_distribution': dict(sorted(Counter(r['alpha'] for r in visited.values()).items())),
              'color_upper_distribution': dict(sorted(Counter(r['color_count'] for r in visited.values()).items())),
              'total_alpha_search_calls': independent_calls,
              'exact_trials': exact_records, 'certificates': list(visited.values())}
    (ROOT / 'factor_s4_directed_search.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items() if k not in ('base_edges', 'permutation_table', 'certificates', 'exact_trials')}), flush=True)


if __name__ == '__main__':
    main()
