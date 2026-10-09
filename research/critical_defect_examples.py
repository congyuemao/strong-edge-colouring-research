"""Explicit local-obstruction models, not counterexamples to 20 colours.

No external libraries. The incidence graph of 1D and 2D subspaces of F_3^3
is constructed directly from normalized nonzero vectors and dot products.
"""

from collections import Counter
from itertools import product, combinations
import json


def canonical(v):
    first = next(x for x in v if x)
    inv = 1 if first == 1 else 2
    return tuple((x * inv) % 3 for x in v)


def conflict_graph(edges, chosen):
    neighbors = {}
    for u, v in edges:
        neighbors.setdefault(u, set()).add(v)
        neighbors.setdefault(v, set()).add(u)
    conflicts = set()
    for i, e in enumerate(chosen):
        for j in range(i):
            f = chosen[j]
            if set(e) & set(f) or any(y in neighbors[x] for x in e for y in f):
                conflicts.add((j, i))
    degrees = [0] * len(chosen)
    for i, j in conflicts:
        degrees[i] += 1
        degrees[j] += 1
    return conflicts, degrees


def main():
    vectors = sorted({canonical(v) for v in product(range(3), repeat=3) if any(v)})
    assert len(vectors) == 13
    edges = [(i, 13 + j) for i, v in enumerate(vectors) for j, w in enumerate(vectors)
             if sum(x * y for x, y in zip(v, w)) % 3 == 0]
    assert len(edges) == 52
    adjacency = [set() for _ in range(26)]
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    assert all(len(n) == 4 for n in adjacency)
    assert all(len(adjacency[x] & adjacency[y]) <= 1
               for x, y in combinations(range(26), 2))
    _, full_degrees = conflict_graph(edges, edges)
    assert set(full_degrees) == {24}

    removed = edges[0]
    chosen = edges[1:]
    old_conflicts, old_degrees = conflict_graph(edges, chosen)
    new_conflicts, new_degrees = conflict_graph(chosen, chosen)
    assert set(old_degrees) == {23, 24}
    assert min(new_degrees) == 20
    assert new_conflicts <= old_conflicts
    lost = old_conflicts - new_conflicts
    assert len(lost) == 9
    u, v = removed
    for i, j in lost:
        e, f = chosen[i], chosen[j]
        assert ((u in e and v in f) or (v in e and u in f))
    report = {
        "meaning": "Local necessary conditions do not eliminate a connector leaf or degree-three vertices.",
        "warning": "Neither example is claimed to have a 21-critical conflict graph.",
        "vertices": 26,
        "edges": edges,
        "removed_edge": removed,
        "original_full_conflict_degrees": dict(sorted(Counter(full_degrees).items())),
        "F_with_connector_retained_degrees": dict(sorted(Counter(old_degrees).items())),
        "F_with_connector_deleted_degrees": dict(sorted(Counter(new_degrees).items())),
        "lost_conflict_pairs": [[chosen[i], chosen[j]] for i, j in sorted(lost)],
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
