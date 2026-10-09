"""Exact factor-restricted conflict colourings. Python standard library only.

All conflicts are computed in the original four-regular graph, never merely
inside the factor. Enumeration/certificates concern finite examples only.
"""
from itertools import combinations
from pathlib import Path
import json
import random


def edge(u, v):
    return tuple(sorted((u, v)))


def conflicts(n, all_edges, chosen):
    adj = [set() for _ in range(n)]
    for u, v in all_edges:
        adj[u].add(v)
        adj[v].add(u)
    out = [0] * len(chosen)
    for i, (u, v) in enumerate(chosen):
        for j, (x, y) in enumerate(chosen[:i]):
            if (len({u, v, x, y}) < 4 or x in adj[u] or y in adj[u]
                    or x in adj[v] or y in adj[v]):
                out[i] |= 1 << j
                out[j] |= 1 << i
    return out


def largest_clique(adj):
    best = []

    def visit(clique, candidates):
        nonlocal best
        if len(clique) + candidates.bit_count() <= len(best):
            return
        if not candidates:
            best = clique
            return
        while candidates:
            if len(clique) + candidates.bit_count() <= len(best):
                return
            bit = candidates & -candidates
            candidates -= bit
            v = bit.bit_length() - 1
            visit(clique + [v], candidates & adj[v])
    visit([], (1 << len(adj)) - 1)
    return best


def exact_colouring(adj):
    n = len(adj)
    colours = [-1] * n

    def allowed(v):
        used = 0
        bits = adj[v]
        while bits:
            bit = bits & -bits
            bits -= bit
            c = colours[bit.bit_length() - 1]
            if c >= 0:
                used |= 1 << c
        return used

    for _ in range(n):
        v = max((v for v in range(n) if colours[v] < 0),
                key=lambda v: (allowed(v).bit_count(), adj[v].bit_count()))
        mask = allowed(v)
        c = 0
        while mask & (1 << c):
            c += 1
        colours[v] = c
    upper = max(colours, default=-1) + 1
    best = colours[:]
    clique = largest_clique(adj)
    lower = len(clique)

    def search(k, remaining, used_count):
        if not remaining:
            return colours[:]
        v = max((v for v in range(n) if remaining & (1 << v)),
                key=lambda v: (allowed(v).bit_count(),
                               (adj[v] & remaining).bit_count()))
        banned = allowed(v)
        if banned.bit_count() >= k:
            return None
        for c in range(min(k, used_count + 1)):
            if banned & (1 << c):
                continue
            colours[v] = c
            found = search(k, remaining ^ (1 << v), max(used_count, c + 1))
            if found is not None:
                return found
        colours[v] = -1
        return None

    for k in range(lower, upper):
        colours[:] = [-1] * n
        remaining = (1 << n) - 1
        for c, v in enumerate(clique):
            colours[v] = c
            remaining ^= 1 << v
        found = search(k, remaining, len(clique))
        if found is not None:
            return k, found, clique
    return upper, best, clique


def factors(n, edges):
    incident = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        incident[u].append(i)
        incident[v].append(i)
    assert all(len(xs) == 4 for xs in incident)
    state = [-1] * len(edges)
    deg = [0] * n

    def visit():
        candidates = []
        for v in range(n):
            free = [i for i in incident[v] if state[i] == -1]
            need = 2 - deg[v]
            if need < 0 or need > len(free):
                return
            if free:
                candidates.append((len(list(combinations(free, need))),
                                   len(free), v, free, need))
        if not candidates:
            yield tuple(i for i, s in enumerate(state) if s == 1)
            return
        _, _, v, free, need = min(candidates)
        for chosen in combinations(free, need):
            chosen = set(chosen)
            for i in free:
                state[i] = int(i in chosen)
                if state[i]:
                    for x in edges[i]:
                        deg[x] += 1
            yield from visit()
            for i in free:
                if state[i]:
                    for x in edges[i]:
                        deg[x] -= 1
                state[i] = -1
    yield from visit()


def analyse(n, edges):
    cache = {}
    results = []
    all_ids = set(range(len(edges)))
    for ids in factors(n, edges):
        # Suppress factor-swap duplicates.
        if 0 not in ids:
            continue
        other = tuple(sorted(all_ids - set(ids)))
        row = []
        for subset in (ids, other):
            adj = conflicts(n, edges, [edges[i] for i in subset])
            signature = tuple(adj)
            if signature not in cache:
                k, colours, clique = exact_colouring(adj)
                # Independent endpoint-formula checks use all original edges.
                assert all(colours[i] != colours[j]
                           for i in range(n) for j in range(i)
                           if adj[i] & (1 << j))
                cache[signature] = (k, colours, clique)
            k, colours, clique = cache[signature]
            row.append(dict(edges=[edges[i] for i in subset], chi=k,
                            colours=colours, clique=clique))
        results.append(dict(sum=sum(r['chi'] for r in row), factors=row))
    return dict(n=n, edges=edges, count=len(results),
                minimum=min(r['sum'] for r in results),
                maximum=max(r['sum'] for r in results),
                distribution={str(k): sum(r['sum'] == k for r in results)
                              for k in sorted({r['sum'] for r in results})},
                best=min(results, key=lambda r: r['sum']),
                worst=max(results, key=lambda r: r['sum']))


if __name__ == '__main__':
    n = 11
    edges = sorted({edge(i, (i+s) % n) for i in range(n) for s in (1, 4)})
    result = analyse(n, edges)
    target = Path(__file__).with_name('structural_factors.json')
    target.write_text(json.dumps(result, indent=2), encoding='utf-8')
    print({k: result[k] for k in ('n', 'count', 'minimum', 'maximum', 'distribution')})
