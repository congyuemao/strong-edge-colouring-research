"""Exhaust the small port choices for a Moser matching-conflict graph.

This is used to locate an explicit mathematical obstruction to an overly
strong intermediate assertion, not as a proof of a coloring upper bound.
"""
from itertools import product
from pathlib import Path
import json


def solve():
    names = ['v', 'a', 'b', 'c', 'd', 'e', 'f']
    edges = [('a','b'), ('a','c'), ('b','c'), ('d','e'), ('d','f'),
             ('e','f'), ('a','d'), ('v','b'), ('v','c'), ('v','e'), ('v','f')]
    index = {x:i for i,x in enumerate(names)}
    hedges = [(index[x], index[y]) for x,y in edges]
    adj = [sorted(w for e in hedges for w in e if v in e and w != v)
           for v in range(7)]
    choices = []
    for v, ns in enumerate(adj):
        options = []
        for bits in product(range(2), repeat=len(ns)-1):
            bits = (0,) + bits
            if max(bits.count(0), bits.count(1)) > 3 or not bits.count(1):
                continue
            # Deliberately seek a realization with only seven degree>=3
            # original vertices, ruling out a Petersen-minus-edge subgraph.
            if v == 0 and sorted([bits.count(0), bits.count(1)]) != [1, 3]:
                continue
            options.append(dict(zip(ns, bits)))
        choices.append(options)
    examined = 0
    for ports in product(*choices):
        examined += 1
        gedges = [(2*v,2*v+1) for v in range(7)]
        gedges += [(2*u+ports[u][v], 2*v+ports[v][u]) for u,v in hedges]
        gadj = [set() for _ in range(14)]
        for u,v in gedges:
            gadj[u].add(v)
            gadj[v].add(u)
        if any(gadj[u] & gadj[v] for u,v in gedges):
            continue
        if any(len(gadj[u] & gadj[v]) >= 2
               for u in range(14) for v in range(u+1,14)):
            continue
        # Recompute every pair of matching edges directly from original G.
        actual = {(u,v) for u in range(7) for v in range(u+1,7)
                  if any(y in gadj[x] for x in (2*u,2*u+1)
                         for y in (2*v,2*v+1))}
        assert actual == {tuple(sorted(e)) for e in hedges}
        degree = [len(a) for a in gadj]
        assert sum(d >= 3 for d in degree) == 7
        return {'examined': examined, 'names': names, 'edges': gedges,
                'degrees': degree, 'ports': ports,
                'matching_conflicts': sorted(actual)}
    return {'examined': examined, 'found': False}


if __name__ == '__main__':
    result = solve()
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result))
