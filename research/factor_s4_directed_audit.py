"""Rebuild S4 experiment from JSON, without importing the search routines.

Check every color certificate and exact alpha via a separate include/exclude
algorithm. Replay the one five-color impossibility using fixed-clique MRV.
"""
from itertools import combinations
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent


def independent_number(masks):
    best = 0
    calls = 0

    def clique_cover_bound(candidates):
        bound = 0
        while candidates:
            bound += 1
            allowed = candidates
            while allowed:
                bit = allowed & -allowed
                v = bit.bit_length() - 1
                candidates ^= bit
                allowed &= candidates & masks[v]
        return bound

    def search(candidates, used):
        nonlocal best, calls
        calls += 1
        if used + clique_cover_bound(candidates) <= best:
            return
        if not candidates:
            best = max(best, used)
            return
        vertices = [v for v in range(44) if candidates >> v & 1]
        v = max(vertices, key=lambda v: (masks[v] & candidates).bit_count())
        search(candidates & ~(masks[v] | (1 << v)), used + 1)
        search(candidates & ~(1 << v), used)
    search((1 << 44) - 1, 0)
    return best, calls


def five_color(masks):
    # Any five-clique uses all five colors, so its labels can be fixed.
    anchor = next(q for q in combinations(range(44), 5)
                  if all(masks[i] >> j & 1 for i, j in combinations(q, 2)))
    colors = {v: i for i, v in enumerate(anchor)}
    calls = 0

    def search():
        nonlocal calls
        calls += 1
        if len(colors) == 44:
            return True
        domains = {v: set(range(5)) - {colors[u] for u in colors if masks[v] >> u & 1}
                   for v in range(44) if v not in colors}
        v = min(domains, key=lambda v: (len(domains[v]), v))
        for c in sorted(domains[v]):
            colors[v] = c
            if search():
                return True
            del colors[v]
        return False
    answer = search()
    return answer, calls, list(anchor)


def main():
    data = json.loads((ROOT / 'factor_s4_directed_search.json').read_text(encoding='utf-8'))
    unsat = {tuple(r['permutation_indices']) for r in data['exact_trials']
             if any(t['status'] == 'unsat' and t['k'] == 5 for t in r['trials'])}
    results = []
    for row in data['certificates']:
        perms = [tuple(range(4))] * 10 + row['permutations']
        assert all(sorted(p) == list(range(4)) for p in perms)
        edges = [(4 * a + x, 4 * b + perms[j][x])
                 for j, (a, b) in enumerate(data['base_edges']) for x in range(4)]
        factor = edges[:44]
        assert len(set(map(frozenset, edges))) == 88
        adj = [set() for _ in range(44)]
        for a, b in edges:
            adj[a].add(b)
            adj[b].add(a)
        assert all(len(ns) == 4 for ns in adj)
        assert all(not adj[a] & adj[b] for a, b in edges)
        assert all(len(adj[a] & adj[b]) <= 1 for a in range(44) for b in range(a))
        masks = [0] * 44
        for i, j in combinations(range(44), 2):
            a, b = factor[i]
            c, d = factor[j]
            if (len({a, b, c, d}) < 4 or c in adj[a] or d in adj[a]
                    or c in adj[b] or d in adj[b]):
                masks[i] |= 1 << j
                masks[j] |= 1 << i
                assert row['coloring'][i] != row['coloring'][j]
        assert len(row['coloring']) == 44
        assert max(row['coloring']) + 1 == row['color_count'] <= 7
        alpha, calls = independent_number(masks)
        assert alpha == row['alpha']
        record = {'permutation_indices': row['permutation_indices'],
                  'alpha': alpha, 'independent_alpha_search_calls': calls}
        if tuple(row['permutation_indices']) in unsat:
            answer, nodes, anchor = five_color(masks)
            assert not answer
            record['five_color_unsat'] = {'nodes': nodes, 'fixed_clique': anchor}
        results.append(record)
    report = {'all_checks_passed': True, 'certificates_verified': len(results),
              'alpha_search_calls': sum(r['independent_alpha_search_calls'] for r in results),
              'five_color_unsat_replayed': len(unsat), 'records': results}
    (ROOT / 'factor_s4_directed_audit.json').write_text(json.dumps(report, indent=2), encoding='utf-8')
    print(json.dumps({k: v for k, v in report.items() if k != 'records'}), flush=True)


if __name__ == '__main__':
    main()
