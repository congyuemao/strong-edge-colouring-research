"""Exact endpoint search for an induced four-rim wheel in H_F, girth >= 6.

Five named F edges: 0 is hub; 1,2,3,4 cyclic rim.  Enumerate all
linear-forest shapes on these edges and all labellings.  Since G has girth
>=6, these five F edges cannot themselves contain a cycle.  Every required
conflict has a connector inside their endpoint set.  Only minimal connector
witnesses need be searched.  Test that additional connector edges can be
assigned to F so the endpoint degrees can be completed to 4/2 by new trees.
"""
from itertools import combinations, permutations
from pathlib import Path
import json

WHEEL = {(0, i) for i in range(1, 5)} | {(1, 2), (2, 3), (3, 4), (1, 4)}
SHAPES = [(5,), (4, 1), (3, 2), (3, 1, 1), (2, 2, 1),
          (2, 1, 1, 1), (1,) * 5]


def adjacency(n, edges):
    a = [set() for _ in range(n)]
    for u, v in edges:
        a[u].add(v)
        a[v].add(u)
    return a


def conflict(a, e, f):
    return bool(set(e) & set(f)) or any(v in a[u] for u in e for v in f)


def short_path(a, u, v):
    seen, front = {u}, {u}
    for _ in range(4):
        front = set().union(*(a[t] for t in front)) - seen
        if v in front:
            return True
        seen |= front
    return False


def red_completion(n, edges, q):
    red = set(q)
    ga, fa = adjacency(n, edges), adjacency(n, red)
    options = [e for e in edges - red if all(len(fa[v]) == 1 for v in e)]
    forced = {v for v in range(n) if len(ga[v]) == 4 and len(fa[v]) == 1}
    def rec(i, occupied, picked):
        if forced <= occupied:
            return sorted(red | set(picked))
        if i == len(options):
            return None
        e = options[i]
        if not occupied.intersection(e):
            out = rec(i + 1, occupied | set(e), picked + [e])
            if out is not None:
                return out
        return rec(i + 1, occupied, picked)
    return rec(0, set(), [])


def inspect(n, q):
    initial = frozenset(q)
    a = adjacency(n, initial)
    if any(conflict(a, q[i], q[j]) for i, j in combinations(range(5), 2)
           if (i, j) not in WHEEL):
        return None, 0
    seen = set()
    def dfs(edges):
        if edges in seen:
            return None
        seen.add(edges)
        a = adjacency(n, edges)
        needed = []
        for i, j in sorted(WHEEL):
            if conflict(a, q[i], q[j]):
                continue
            choices = set()
            for u in q[i]:
                for v in q[j]:
                    if u == v or v in a[u] or len(a[u]) == 4 or len(a[v]) == 4:
                        continue
                    if short_path(a, u, v):
                        continue
                    e = tuple(sorted((u, v)))
                    aa = adjacency(n, edges | {e})
                    if any(conflict(aa, q[s], q[t])
                           for s, t in combinations(range(5), 2)
                           if (s, t) not in WHEEL):
                        continue
                    choices.add(e)
            if not choices:
                return None
            needed.append(choices)
        if not needed:
            f = red_completion(n, edges, q)
            if f is not None:
                return {'n': n, 'edges': sorted(edges), 'F': f,
                        'named_edges': q}
            return None
        for e in sorted(min(needed, key=len)):
            out = dfs(edges | {e})
            if out is not None:
                return out
        return None
    return dfs(initial), len(seen)


def verify(row):
    n, edges, f, q = row['n'], set(map(tuple, row['edges'])), set(map(tuple, row['F'])), row['named_edges']
    a, fa = adjacency(n, edges), adjacency(n, f)
    assert f <= edges and all(tuple(e) in f for e in q)
    assert max(map(len, a)) <= 4 and max(map(len, fa)) <= 2
    assert all(len(a[v]) - len(fa[v]) <= 2 for v in range(n))
    for u, v in edges:
        assert not short_path(adjacency(n, edges - {(u, v)}), u, v)
    got = {(i, j) for i, j in combinations(range(5), 2) if conflict(a, q[i], q[j])}
    assert got == WHEEL


def main():
    nodes = cases = 0
    result = {'scope': 'First witness, or exhaustive absence among all five-edge endpoint models',
              'wheel_edges': sorted(WHEEL), 'witness': None}
    for shape in SHAPES:
        raw, offset = [], 0
        for length in shape:
            raw.extend((offset + i, offset + i + 1) for i in range(length))
            offset += length + 1
        for perm in permutations(range(5)):
            q = [raw[i] for i in perm]
            row, count = inspect(offset, q)
            nodes += count
            cases += 1
            if row is not None:
                verify(row)
                result.update(witness=row, shape=shape, cases=cases, nodes=nodes)
                Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
                print(json.dumps(result))
                return
    result.update(cases=cases, nodes=nodes)
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
