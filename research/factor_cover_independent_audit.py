"""Independent cover enumeration and raw-endpoint certificate audit.

Does not import any generator, conflict-graph routine, or coloring solver.
Enumerates permutations by prefix DFS with direct monodromy composition;
no linear-form propagation used by the original search is reused.
"""
from collections import Counter
from itertools import combinations, permutations, product
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = [(v, (v + 1) % 11) for v in range(11)]
BASE += [(v, (v + 4) % 11) for v in range(11)]
INDEX = {frozenset(e): j for j, e in enumerate(BASE)}
ADJ = [set() for _ in range(11)]
for u, v in BASE:
    ADJ[u].add(v)
    ADJ[v].add(u)


def canonical(seq):
    seq = tuple(seq)
    rev = seq[::-1]
    return min(s[k:] + s[:k] for s in (seq, rev) for k in range(len(s)))


def closed_walks(length):
    """Enumerate all cyclically nonbacktracking closed walks, allowing repeats."""
    result = []
    for start in range(11):
        def extend(path):
            if len(path) == length:
                if start in ADJ[path[-1]] and path[-2] != start and path[-1] != path[1]:
                    result.append(tuple(path))
                return
            for nxt in sorted(ADJ[path[-1]]):
                if len(path) > 1 and nxt == path[-2]:
                    continue
                extend(path + [nxt])
        extend([start])
    return result


WALKS3 = closed_walks(3)
WALKS4 = closed_walks(4)
assert not WALKS3
assert all(len(set(w)) == 4 for w in WALKS4)
CYCLES = sorted({canonical(w) for w in WALKS4})
assert len(WALKS4) == 8 * len(CYCLES) == 176
listed = {canonical(tuple((i + a) % 11 for a in template))
          for i in range(11) for template in ((0, 1, 5, 4), (0, 4, 8, 1))}
assert set(CYCLES) == listed
PATHS = []
for cyc in CYCLES:
    path = []
    for u, v in zip(cyc, cyc[1:] + cyc[:1]):
        j = INDEX[frozenset((u, v))]
        path.append((j, BASE[j] == (u, v)))
    PATHS.append(path)


def inverse(p):
    return tuple(p.index(x) for x in range(len(p)))


def monodromy_has_fixed_point(path, choices, p):
    for origin in range(p):
        x = origin
        for j, forward in path:
            if j < 10:
                continue
            perm, inv = choices[j - 10]
            x = (perm if forward else inv)[x]
        if x == origin:
            return True
    return False


def enumerate_assignments(p, signs=None):
    """All p^12 normalized shifts, reject only completed cycle monodromies."""
    signs = signs or [1] * 12
    domains = []
    for s in signs:
        domain = []
        for b in range(p):
            perm = tuple((s * x + b) % p for x in range(p))
            domain.append((perm, inverse(perm)))
        domains.append(domain)
    checks = [[] for _ in range(12)]
    for path in PATHS:
        last = max(j - 10 for j, _ in path if j >= 10)
        checks[last].append(path)
    chosen = [None] * 12
    digits = [0] * 12
    solutions = set()
    nodes = 0
    covered_assignments = 0

    def visit(i):
        nonlocal nodes, covered_assignments
        nodes += 1
        for b, perm in enumerate(domains[i]):
            chosen[i] = perm
            digits[i] = b
            if any(monodromy_has_fixed_point(path, chosen, p) for path in checks[i]):
                covered_assignments += p ** (11 - i)
                continue
            if i == 11:
                solutions.add(tuple(digits))
                covered_assignments += 1
            else:
                visit(i + 1)
    visit(0)
    assert covered_assignments == p ** 12
    return solutions, {'prefix_nodes': nodes, 'covered_assignments': covered_assignments,
                       'solutions': len(solutions)}


def permutation_parity(perm):
    return sum(perm[i] > perm[j] for i in range(3) for j in range(i + 1, 3)) % 2


def admissible_sign_masks():
    masks = []
    for mask in range(4096):
        valid = True
        for path in PATHS:
            bit = 0
            for j, _ in path:
                if j >= 10:
                    bit ^= (mask >> (j - 10)) & 1
            if bit:
                valid = False
                break
        if valid:
            masks.append(mask)
    return masks


def raw_graph(p, digits, signs=None):
    """Rebuild using explicit matching tables, no generator functions."""
    signs = signs or [1] * 12
    all_edges = []
    red_edges = []
    for j, (u, v) in enumerate(BASE):
        table = tuple(range(p)) if j < 10 else tuple(
            (signs[j - 10] * x + digits[j - 10]) % p for x in range(p))
        for a, b in enumerate(table):
            edge = (p * u + a, p * v + b)
            all_edges.append(edge)
            if j < 11:
                red_edges.append(edge)
    return all_edges, red_edges


def check_certificate(p, digits, colors, count, signs=None, saved_edges=None, saved_factor=None):
    edges, red = raw_graph(p, digits, signs)
    n = 11 * p
    assert len(edges) == 2 * n and len(red) == n
    assert len({frozenset(e) for e in edges}) == len(edges)
    assert all(a != b and 0 <= a < n and 0 <= b < n for a, b in edges)
    adj = [set() for _ in range(n)]
    reddegree = [0] * n
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    for a, b in red:
        reddegree[a] += 1
        reddegree[b] += 1
    assert all(len(a) == 4 for a in adj)
    assert reddegree == [2] * n
    # Triangles: adjacent vertices have no common neighbor.
    assert all(not (adj[a] & adj[b]) for a, b in edges)
    # A repeated pair of neighbors at two centers is exactly a four-cycle.
    seen_neighbor_pairs = set()
    for ns in adj:
        for a, b in combinations(sorted(ns), 2):
            assert (a, b) not in seen_neighbor_pairs
            seen_neighbor_pairs.add((a, b))
    assert colors is not None and len(colors) == n
    assert set(colors) <= set(range(10)) and len(set(colors)) == count
    if saved_edges is not None:
        assert [tuple(e) for e in saved_edges] == edges
    if saved_factor is not None:
        assert [tuple(e) for e in saved_factor] == red
    conflict_degree = [0] * n
    for i, (a, b) in enumerate(red):
        for j in range(i):
            c, d = red[j]
            conflict = (a == c or a == d or b == c or b == d or
                        c in adj[a] or d in adj[a] or c in adj[b] or d in adj[b])
            if conflict:
                conflict_degree[i] += 1
                conflict_degree[j] += 1
                assert colors[i] != colors[j]
    assert conflict_degree == [12] * n


def main():
    summary = {'base_triangular_nonbacktracking_walks': len(WALKS3),
               'base_quadrangular_nonbacktracking_walks': len(WALKS4),
               'base_simple_four_cycles': len(CYCLES)}
    p3 = list(permutations(range(3)))
    affine = {tuple((s * x + b) % 3 for x in range(3))
              for s in (1, -1) for b in range(3)}
    assert affine == set(p3)
    derangements = [p for p in p3 if all(p[x] != x for x in range(3))]
    assert len(derangements) == 2
    assert all(permutation_parity(p) == 0 for p in derangements)
    masks = admissible_sign_masks()
    assert masks == [0, 255]
    summary['three_sheet_sign_masks'] = masks

    binary, counts = enumerate_assignments(2)
    data = json.loads((ROOT / 'factor_double_lift_search.json').read_text(encoding='utf-8'))
    stored = {tuple((r['voltage_mask'] >> j) & 1 for j in range(12))
              for r in data['certificates']}
    assert binary == stored and len(binary) == data['valid_lifts'] == 0
    summary['double'] = counts
    print('double', counts, flush=True)

    triple = json.loads((ROOT / 'factor_triple_permutation_lifts.json').read_text(encoding='utf-8'))
    assert triple['normalized_permutation_assignments'] == 6 ** 12
    assert [tuple(e) for e in triple['base_edges']] == BASE
    assert len(triple['certificates']) == triple['valid_girth_five_lifts']
    summary['triple'] = {}
    for mask in masks:
        signs = [-1 if mask & (1 << j) else 1 for j in range(12)]
        sols, counts = enumerate_assignments(3, signs)
        records = [r for r in triple['certificates'] if r['sign_mask'] == mask]
        assert len(records) == len(sols)
        assert sols == {tuple(r['shifts']) for r in records}
        for r in records:
            check_certificate(3, r['shifts'], r['colors'], r['color_count'], signs)
            assert r['ten_color_search_nodes'] == 0
        counts['color_distribution'] = dict(sorted(Counter(r['color_count'] for r in records).items()))
        summary['triple'][str(mask)] = counts
        print('triple', mask, counts, flush=True)
        if mask == 0:
            cyclic3 = json.loads((ROOT / 'factor_cyclic_lift_3.json').read_text(encoding='utf-8'))
            assert sols == {tuple(r['voltages']) for r in cyclic3['certificates']}
            assert len(sols) == cyclic3['valid_girth_five_lifts'] == 0

    sols, counts = enumerate_assignments(4)
    data = json.loads((ROOT / 'factor_cyclic_lift_4.json').read_text(encoding='utf-8'))
    assert data['modulus'] == 4 and data['all_normalized_assignments'] == 4 ** 12
    assert [tuple(e) for e in data['base_edges']] == BASE
    records = data['certificates']
    assert len(records) == len(sols) == data['valid_girth_five_lifts']
    assert sols == {tuple(r['voltages']) for r in records}
    for i, r in enumerate(records):
        check_certificate(4, r['voltages'], r['coloring'], r['number_of_colors'])
        assert r['ten_color_search_nodes'] == 0
        if (i + 1) % 2000 == 0:
            print('four-sheet certificates checked:', i + 1, flush=True)
    counts['color_distribution'] = dict(sorted(Counter(r['number_of_colors'] for r in records).items()))
    summary['cyclic_four'] = counts
    summary['all_checks_passed'] = True
    (ROOT / 'factor_cover_independent_audit.json').write_text(
        json.dumps(summary, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(summary, ensure_ascii=False), flush=True)


if __name__ == '__main__':
    main()
