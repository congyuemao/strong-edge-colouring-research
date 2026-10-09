"""Search a 4+8+8 decomposition of the existing 40-vertex test graph.

Finite experiment only; independent verifier checks each certificate.
"""
from itertools import combinations
import json
from pathlib import Path
import random
from short_path_reservoir import maximum_clique


def two_short_forests(n, edges):
    incident = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        incident[u].append(i)
        incident[v].append(i)
    clauses = set()
    for star in incident:
        clauses.update(tuple(sorted(c)) for c in combinations(star, 3))
    for middle, (u, v) in enumerate(edges):
        for first in incident[u]:
            for last in incident[v]:
                if len({first, middle, last}) == 3:
                    clauses.add(tuple(sorted((first, middle, last))))
    clauses = list(clauses)
    containing = [[] for _ in edges]
    for i, clause in enumerate(clauses):
        for v in clause:
            containing[v].append(i)
    visits = 0

    def solve(assignment, pending):
        nonlocal visits
        visits += 1
        if visits > 100000:
            return None
        while pending:
            v, color = pending.pop()
            if assignment[v] >= 0:
                if assignment[v] != color:
                    return None
                continue
            assignment[v] = color
            for ci in containing[v]:
                clause = clauses[ci]
                values = [assignment[w] for w in clause]
                if all(c == values[0] for c in values) and values[0] >= 0:
                    return None
                for c in (0, 1):
                    if values.count(c) == 2 and -1 in values:
                        pending.append((clause[values.index(-1)], 1-c))
        remaining = [v for v, c in enumerate(assignment) if c < 0]
        if not remaining:
            return assignment
        v = max(remaining, key=lambda w: sum(
            any(assignment[z] >= 0 for z in clauses[ci])
            for ci in containing[w]))
        for color in (0, 1):
            result = solve(assignment[:], [(v, color)])
            if result is not None:
                return result
        return None

    return solve([-1] * len(edges), [(0, 0)]) if edges else []


def main():
    data = json.loads(Path(__file__).with_name('regular_core_cover.json')
                      .read_text(encoding='utf-8'))
    edges, n = data['edges'], data['vertices']
    adjacency = [set() for _ in range(n)]
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    compatible = [0] * len(edges)
    for i, (u, v) in enumerate(edges):
        for j, (x, y) in enumerate(edges):
            if (len({u, v, x, y}) == 4 and x not in adjacency[u]
                    and y not in adjacency[u] and x not in adjacency[v]
                    and y not in adjacency[v]):
                compatible[i] |= 1 << j
    rng = random.Random(9701)
    for attempt in range(50):
        remaining = list(range(len(edges)))
        classes = []
        for color in range(4):
            rng.shuffle(remaining)
            local = [sum(1 << j for j, f in enumerate(remaining)
                         if compatible[e] & (1 << f)) for e in remaining]
            clique, _ = maximum_clique(local)
            chosen = {remaining[i] for i in clique}
            classes.append(sorted(chosen))
            remaining = [e for e in remaining if e not in chosen]
        remaining.sort()
        assignment = two_short_forests(n, [edges[e] for e in remaining])
        print(json.dumps({'attempt': attempt,
                          'class_sizes': [len(c) for c in classes],
                          'remaining': len(remaining),
                          'decomposition': assignment is not None}), flush=True)
        if assignment is not None:
            forest_classes = [[remaining[i] for i, c in enumerate(assignment)
                               if c == color] for color in (0, 1)]
            assert len(set(sum(classes + forest_classes, []))) == len(edges)
            for part in classes:
                assert all(compatible[e] & (1 << f)
                           for e in part for f in part if e != f)
            for part in forest_classes:
                inc = [[] for _ in range(n)]
                for e in part:
                    for v in edges[e]:
                        inc[v].append(e)
                assert max(map(len, inc)) <= 2
                for e in part:
                    u, v = edges[e]
                    assert not (len(inc[u]) == len(inc[v]) == 2)
            output = {'source': 'regular_core_cover.json', 'attempt': attempt,
                      'strong_color_classes': classes,
                      'short_path_classes': forest_classes,
                      'class_sizes': [len(c) for c in classes + forest_classes],
                      'vertices': n, 'edges': edges}
            Path(__file__).with_suffix('.json').write_text(
                json.dumps(output, indent=2), encoding='utf-8')
            return


if __name__ == '__main__':
    main()
