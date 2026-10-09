"""Independent integer coefficient and original-edge verification for P-e.

No color-assignment symmetry reduction is used.  All interpolation weights
are integers after multiplication by the product of the factorials.
"""
from itertools import combinations
from math import comb, factorial, prod
from pathlib import Path
import json


def original_model():
    vertices = list(combinations(range(1, 6), 2))
    edges = [tuple(sorted((a, b))) for a, b in combinations(vertices, 2)
             if not set(a) & set(b)]
    deleted = ((1, 2), (3, 4))
    edges.remove(deleted)
    adj = {v: set() for v in vertices}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    by_label = {i: [] for i in range(1, 6)}
    for e in edges:
        label, = set(range(1, 6)) - set(e[0]) - set(e[1])
        by_label[label].append(e)
    specials = []
    normal_pairs = []
    for label in (4, 3, 2, 1):
        special, = [e for e in by_label[label] if any(v in deleted for v in e)]
        specials.append(special)
        normal_pairs.append([e for e in by_label[label] if e != special])
    normal_pairs.append(by_label[5])
    order = specials + [e for pair in normal_pairs for e in pair]
    conflicts = []
    for i, j in combinations(range(14), 2):
        e, f = order[i], order[j]
        if set(e) & set(f) or any(y in adj[x] for x in e for y in f):
            conflicts.append((i, j))
    parts = [[i, 4+2*i, 5+2*i] for i in range(4)] + [[12, 13]]
    block = {v: i for i, part in enumerate(parts) for v in part}
    model = [(i, j) for i, j in combinations(range(14), 2)
             if block[i] != block[j] and not (i in (0, 1) and j in (2, 3))]
    assert model == conflicts
    distances = {}
    for a in vertices:
        d = {a: 0}
        todo = [a]
        for x in todo:
            for y in adj[x]:
                if y not in d:
                    d[y] = d[x] + 1
                    todo.append(y)
        distances[a] = d
    long_pairs = [(a, b) for a, b in combinations(vertices, 2)
                  if distances[a][b] >= 4]
    assert long_pairs == [deleted]
    return order, conflicts


def integer_coefficient():
    t = [4]*4 + [5, 6, 6, 6, 5, 6, 6, 6] + [6, 6]
    assert sum(t) == 74
    weights = [[(-1)**(n-c)*comb(n, c) for c in range(n+1)] for n in t]
    total = count = 0
    pairs = []

    def rec(part, used, factor):
        nonlocal total, count
        if part == 5:
            count += 1
            moments = []
            for i in range(4):
                zero = first = 0
                for c in range(t[i]+1):
                    term = weights[i][c]
                    for j, pair in enumerate(pairs):
                        if i != j:
                            for x in pair:
                                term *= c-x
                    zero += term
                    first += c*term
                moments.append((zero, first))
            total += factor * (moments[0][1]*moments[1][0] -
                               moments[0][0]*moments[1][1]) * (
                               moments[2][1]*moments[3][0] -
                               moments[2][0]*moments[3][1])
            return
        ia, ib = 4+2*part, 5+2*part
        for a in range(t[ia]+1):
            if a in used:
                continue
            for b in range(t[ib]+1):
                if b in used:
                    continue
                value = factor*weights[ia][a]*weights[ib][b]
                for x, y in pairs:
                    value *= (x-a)*(x-b)*(y-a)*(y-b)
                pairs.append((a, b))
                rec(part+1, used | {a, b}, value)
                pairs.pop()

    rec(0, set(), 1)
    denominator = prod(factorial(n) for n in t)
    assert total % denominator == 0
    return {"exponents": t, "ordered_normal_assignments": count,
            "integer_numerator": total, "denominator": denominator,
            "coefficient": total//denominator}


if __name__ == '__main__':
    order, conflicts = original_model()
    result = integer_coefficient()
    result["original_edges_in_order"] = order
    result["conflict_edges"] = conflicts
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('original_edges_in_order', 'conflict_edges')}))
