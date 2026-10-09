"""Independent endpoint model and unfactored exact interpolation verification.

Does not import the coefficient generator.  It reconstructs Petersen-minus-edge
from two-subsets and enumerates every nonzero grid assignment directly.
"""
from itertools import combinations
from math import comb, factorial, prod
from pathlib import Path
import json


def main():
    pairs = list(combinations(range(5), 2))
    graph = [(i, j) for i in range(10) for j in range(i+1, 10)
             if not set(pairs[i]) & set(pairs[j])]
    u, v = pairs.index((0, 1)), pairs.index((2, 3))
    missing = tuple(sorted((u, v)))
    graph.remove(missing)
    adj = [set() for _ in pairs]
    for a, b in graph:
        adj[a].add(b)
        adj[b].add(a)
    group_order = [3, 2, 1, 0, 4]
    grouped = {i: [] for i in range(5)}
    for e in graph:
        label = next(iter(set(range(5)) - set(pairs[e[0]]) - set(pairs[e[1]])))
        grouped[label].append(e)
    edge_order = [None]*14
    for p, label in enumerate(group_order):
        if p < 4:
            special = next(e for e in grouped[label] if u in e or v in e)
            edge_order[p] = special
            normal = [e for e in grouped[label] if e != special]
            edge_order[4+2*p:6+2*p] = normal
        else:
            edge_order[12:14] = grouped[label]
    h_edges = []
    for i, e in enumerate(edge_order):
        for j in range(i+1, 14):
            f = edge_order[j]
            if set(e) & set(f) or any(y in adj[x] for x in e for y in f):
                h_edges.append((i, j))
    certificate = json.loads(Path(__file__).with_name(
        'petersen_minus_polynomial.json').read_text(encoding='utf-8'))
    assert sorted(h_edges) == sorted(map(tuple, certificate['edges']))
    t = certificate['exponents']
    assert len(h_edges) == sum(t) == 74
    assert all(a <= b for a, b in zip(t, [4]*4+[6]*8+[7]*2))
    order = list(range(4, 14))+list(range(4))
    position = {v: i for i, v in enumerate(order)}
    previous = [[] for _ in range(14)]
    for i, j in h_edges:
        if position[i] < position[j]:
            previous[j].append((i, 1))
        else:
            previous[i].append((j, -1))
    weights = [[(-1)**(bound-c)*comb(bound, c) for c in range(bound+1)]
               for bound in t]
    colors = [None]*14
    numerator = 0
    nodes = [0]*15

    def visit(depth, weight):
        nonlocal numerator
        nodes[depth] += 1
        if depth == 14:
            numerator += weight
            return
        vertex = order[depth]
        for color in range(t[vertex]+1):
            factor = weights[vertex][color]
            for earlier, sign in previous[vertex]:
                difference = colors[earlier]-color
                if not difference:
                    factor = 0
                    break
                factor *= sign*difference
            if factor:
                colors[vertex] = color
                visit(depth+1, weight*factor)
        colors[vertex] = None

    visit(0, 1)
    denominator = prod(factorial(bound) for bound in t)
    answer, remainder = divmod(numerator, denominator)
    assert remainder == 0 and answer == 12240
    assert answer == certificate['results'][0]['coefficient']
    result = {"coefficient": answer, "integer_numerator": str(numerator),
              "integer_denominator": str(denominator), "nodes_by_depth": nodes,
              "proper_grid_assignments": nodes[-1],
              "petersen_vertices": pairs, "petersen_edges_ordered": edge_order,
              "direct_endpoint_model_matches": True}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2),
                                                  encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('petersen_vertices', 'petersen_edges_ordered')}))


if __name__ == '__main__':
    main()
