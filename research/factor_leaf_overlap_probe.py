"""Probe the leaf-restricted clique overlap graph in the existing tower family."""
from itertools import combinations
from collections import Counter, deque
from pathlib import Path
import json
from factor_five_clique_overlap import audit_graph


def run(m):
    vertices = [(k, i) for k in range(m) for i in range(5)]
    f = [((k, i), (k, (i+1) % 5)) for k, i in vertices]
    blue = [((k, i), ((k+1) % m, 2*i % 5)) for k, i in vertices]
    h = audit_graph(vertices, f + blue, f)
    cliques = set()
    for k in range(m):
        ids = list(range(5*k,5*k+5)) + list(range(5*((k+1)%m),5*((k+1)%m)+5))
        for q in combinations(sorted(ids), 5):
            if all(j in h[i] for i,j in combinations(q,2)):
                cliques.add(q)
    cliques = sorted(cliques)
    kernels = {}
    for i, q in enumerate(cliques):
        degrees = Counter(v for e in q for v in f[e])
        for e in q:
            if min(degrees[v] for v in f[e]) == 1:
                kernel = tuple(x for x in q if x != e)
                kernels.setdefault(kernel, []).append(i)
    adj = [set() for q in cliques]
    for containing in kernels.values():
        assert len(containing) <= 2
        if len(containing) == 2:
            i,j = containing
            adj[i].add(j)
            adj[j].add(i)
    seen, components = set(), []
    colors, parents, odd_cycle = {}, {}, None
    for start in range(len(cliques)):
        if start in seen:
            continue
        queue, component = deque([start]), {start}
        seen.add(start)
        colors[start], parents[start] = 0, None
        while queue:
            i = queue.popleft()
            for j in adj[i]:
                if j not in seen:
                    seen.add(j)
                    component.add(j)
                    colors[j], parents[j] = 1-colors[i], i
                    queue.append(j)
                elif colors[j] == colors[i] and odd_cycle is None:
                    p,q = [i],[j]
                    while parents[p[-1]] is not None:
                        p.append(parents[p[-1]])
                    while parents[q[-1]] is not None:
                        q.append(parents[q[-1]])
                    while len(p)>1 and len(q)>1 and p[-2] == q[-2]:
                        p.pop(); q.pop()
                    assert p[-1] == q[-1]
                    path = p + list(reversed(q[:-1]))
                    assert len(path)%2 == 1
                    assert all(path[(z+1)%len(path)] in adj[v]
                               for z,v in enumerate(path))
                    odd_cycle = [cliques[v] for v in path]
        components.append(len(component))
    result = {'m':m, 'leaf_overlap_degree_counts':dict(Counter(map(len, adj))),
              'components':sorted(components), 'odd_cycle':odd_cycle}
    return result


if __name__ == '__main__':
    data = [run(m) for m in (5,6,7,8,9,11)]
    Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2),encoding='utf-8')
    for d in data:
        print(d['m'], d['leaf_overlap_degree_counts'],
              d['components'], len(d['odd_cycle'] or []))
