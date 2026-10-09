"""Independent finite search for graphs in which EVERY edge conflicts.

For each degree-4 vertex v, label its neighbors 0..3. Other nonisolated
vertices have a nonempty neighborhood type in A={0,1,2,3}.
This search uses necessary conditions only and reports survivors of the
upper bound. It is not a search for arbitrary strong cliques in larger G.
"""
from itertools import combinations
import json

A_PAIRS = list(combinations(range(4), 2))
TYPES = sorted(range(1, 16), key=lambda t: (-t.bit_count(), t))

def type_multisets(caps, index=0, values=()):
    if index == len(TYPES):
        yield values
        return
    t = TYPES[index]
    inds = [i for i in range(4) if t >> i & 1]
    cap = min(caps[i] for i in inds)
    for k in range(cap + 1):
        newcaps = tuple(c - (k if i in inds else 0) for i, c in enumerate(caps))
        yield from type_multisets(newcaps, index + 1, values + (t,) * k)

def search():
    counts = dict(a_graphs=0, multisets=0, vertex_bound=0,
                  forced_fail=0, edge_upper_pass=0)
    survivors = []
    best_upper = (0, None)
    for a_mask in range(64):
        adj = [0] * 4
        a_edges = []
        for k, (i, j) in enumerate(A_PAIRS):
            if a_mask >> k & 1:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
                a_edges.append((i,j))
        counts['a_graphs'] += 1
        caps = tuple(3 - adj[i].bit_count() for i in range(4))
        for ts in type_multisets(caps):
            counts['multisets'] += 1
            if len(ts) < 6:
                continue
            counts['vertex_bound'] += 1
            # A-internal edges versus A-B edges must also conflict.
            fail = False
            for i,j in a_edges:
                for t in ts:
                    for k in range(4):
                        if t >> k & 1 and k not in (i,j):
                            if not (t & ((1<<i)|(1<<j))) and not (adj[k] & ((1<<i)|(1<<j))):
                                fail = True
            if fail:
                counts['forced_fail'] += 1
                continue
            forced = []
            optional = []
            deg = [0]*len(ts)
            possible_deg = [0]*len(ts)
            for x,y in combinations(range(len(ts)),2):
                t,u = ts[x],ts[y]
                mandatory = any((t & ~u) >> i & 1 and
                                (u & ~t) >> j & 1 and
                                not (adj[i] >> j & 1)
                                for i in range(4) for j in range(4))
                possible = t | u == 15
                if mandatory and not possible:
                    fail = True
                    break
                if mandatory:
                    forced.append((x,y))
                    deg[x] += 1
                    deg[y] += 1
                elif possible:
                    optional.append((x,y))
                if possible:
                    possible_deg[x] += 1
                    possible_deg[y] += 1
            residual = [4-t.bit_count() for t in ts]
            if fail or any(d > r for d,r in zip(deg,residual)):
                counts['forced_fail'] += 1
                continue
            edge_upper = (sum(min(d,r) for d,r in zip(possible_deg,residual)) // 2
                          + 4 + len(a_edges) + sum(t.bit_count() for t in ts))
            if edge_upper > best_upper[0]:
                best_upper = (edge_upper, dict(a_mask=a_mask, types=ts, forced=forced, optional=optional))
            if edge_upper >= 21:
                counts['edge_upper_pass'] += 1
                survivors.append(dict(a_mask=a_mask, types=ts, forced=forced,
                                      optional=optional, upper=edge_upper))
    return dict(counts=counts,best_upper=best_upper,survivors=survivors)

if __name__ == '__main__':
    result = search()
    print(json.dumps(result, indent=2))
