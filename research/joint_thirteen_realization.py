"""Direct endpoint certificate for the joint 13-vertex obstruction.

No graph packages; build the partial original graph, then an explicit cyclic
cover of a regular completion. Old edges have voltage zero, so their fibre-0
copy preserves the exact 13-vertex induced conflict graph.
"""
from collections import Counter, deque
from itertools import combinations
from pathlib import Path
import json
import random


def graph(n, edges):
    adj = [set() for _ in range(n)]
    for x, y in edges:
        assert x != y and y not in adj[x]
        adj[x].add(y)
        adj[y].add(x)
    return adj


def girth(adj):
    best = len(adj) + 1
    for root in range(len(adj)):
        dist = [-1] * len(adj)
        parent = [-1] * len(adj)
        dist[root] = 0
        todo = deque([root])
        while todo:
            v = todo.popleft()
            if 2 * dist[v] + 1 >= best:
                continue
            for w in adj[v]:
                if dist[w] < 0:
                    dist[w], parent[w] = dist[v] + 1, v
                    todo.append(w)
                elif parent[v] != w:
                    best = min(best, dist[v] + dist[w] + 1)
    return best if best <= len(adj) else None


def conflict(red, adj):
    result = set()
    for i, j in combinations(range(len(red)), 2):
        e, f = red[i], red[j]
        if set(e) & set(f) or any(y in adj[x] for x in e for y in f):
            result.add((i, j))
    return result


def expected():
    # Vertex order p,q,a,b,c,U0,U1,U2,U3,V0,V1,V2,V3.
    ed = {(i, j) for i, j in combinations(range(5), 2)
          if (i, j) not in ((0, 1), (2, 3))}
    ed |= set(combinations(range(5, 9), 2))
    ed |= set(combinations(range(9, 13), 2))
    for v, ns in ((0, (5, 6)), (1, (7, 8)),
                  (2, (9, 10)), (3, (11, 12))):
        ed |= {(v, w) for w in ns}
    return ed


def complete_colour(n, old, forbidden):
    adj = graph(n, old)
    deficit = [2-len(ns) for ns in adj]
    assert min(deficit) >= 0
    out = set()

    def search():
        if not any(deficit):
            return True
        options = []
        for v in range(n):
            if deficit[v]:
                ns = [w for w in range(n) if w != v and deficit[w]
                      and tuple(sorted((v, w))) not in forbidden | out]
                if len(ns) < deficit[v]:
                    return False
                options.append((len(ns), -deficit[v], v, ns))
        _, _, v, ns = min(options)
        for chosen in combinations(ns, deficit[v]):
            added = [tuple(sorted((v, w))) for w in chosen]
            amount = deficit[v]
            deficit[v] = 0
            for w in chosen:
                deficit[w] -= 1
            out.update(added)
            if search():
                return True
            out.difference_update(added)
            for w in chosen:
                deficit[w] += 1
            deficit[v] = amount
        return False

    assert search()
    return sorted(out)


def short_cycle_forms(n, edges, added):
    adj = graph(n, edges)
    idx = {e: i for i, e in enumerate(added)}
    forms = set()
    counts = Counter()
    for root in range(n):
        def walk(path):
            v = path[-1]
            for w in adj[v]:
                if w == root and 3 <= len(path) <= 5:
                    if path[1] > path[-1]:
                        continue
                    counts[len(path)] += 1
                    coeff = [0]*len(added)
                    cyc = path + [root]
                    for x, y in zip(cyc, cyc[1:]):
                        e = tuple(sorted((x, y)))
                        if e in idx:
                            coeff[idx[e]] += 1 if x < y else -1
                    assert any(coeff)
                    forms.add(tuple(coeff))
                elif w > root and w not in path and len(path) < 5:
                    walk(path + [w])
        walk([root])
    return sorted(forms), dict(sorted(counts.items()))


def main():
    names = ['s','t','alpha','beta','S','T','xi','eta','Z','Zprime',
             'W','Wprime'] + ['leaf'+str(i) for i in range(8)]
    # p,q,a,b,c, then U and V.
    red = [(0,2),(5,7),(1,3),(4,6),(0,1),
           (8,12),(8,13),(9,14),(9,15),
           (10,16),(10,17),(11,18),(11,19)]
    blue = [(0,4),(1,5),(6,7),(2,8),(8,9),(7,9),
            (3,10),(10,11),(6,11)]
    red = [tuple(sorted(e)) for e in red]
    blue = [tuple(sorted(e)) for e in blue]
    old = set(red+blue)
    adj = graph(20, old)
    actual = conflict(red, adj)
    assert actual == expected()
    assert max(map(len, adj)) <= 4
    assert max(map(len, graph(20, red))) <= 2
    assert girth(adj) == 6

    red_added = complete_colour(20, red, old)
    blue_added = complete_colour(20, blue, old | set(red_added))
    added = red_added + blue_added
    full = old | set(added)
    assert all(len(ns) == 4 for ns in graph(20, full))
    assert all(len(ns) == 2 for ns in graph(20, red + red_added))
    assert all(len(ns) == 2 for ns in graph(20, blue + blue_added))
    forms, cycle_counts = short_cycle_forms(20, full, added)
    modulus = 101
    rng = random.Random(130013)
    attempts = 0
    while True:
        attempts += 1
        voltages = [rng.randrange(1, modulus) for _ in added]
        if all(sum(a*b for a,b in zip(f, voltages)) % modulus for f in forms):
            break
    volt = dict(zip(added, voltages))
    lifted = []
    lifted_red = []
    for x,y in sorted(full):
        for k in range(modulus):
            e = (x*modulus+k, y*modulus+(k+volt.get((x,y),0)) % modulus)
            lifted.append(tuple(sorted(e)))
            if (x,y) in set(red+red_added):
                lifted_red.append(tuple(sorted(e)))
    ladj = graph(20*modulus, lifted)
    assert all(len(ns) == 4 for ns in ladj)
    assert all(len(ns) == 2 for ns in graph(20*modulus, lifted_red))
    assert girth(ladj) == 6
    copied_red = [(x*modulus,y*modulus) for x,y in red]
    assert conflict(copied_red, ladj) == expected()
    out = {
        'scope': 'Exact partial and full G/F realization; not an optimal A/B/C partition.',
        'names': names, 'partial_red': red, 'partial_blue': blue,
        'partial_girth': 6, 'conflict_edges': sorted(actual),
        'red_added': red_added, 'blue_added': blue_added,
        'modulus': modulus, 'added_edge_voltages': list(zip(added,voltages)),
        'short_base_cycle_counts': cycle_counts,
        'nonzero_short_cycle_forms': len(forms), 'voltage_attempts': attempts,
        'full_vertices': len(ladj), 'full_edges': len(lifted),
        'full_red_edges': len(lifted_red), 'full_girth': 6,
        'induced_13_preserved': True,
    }
    Path(__file__).with_suffix('.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k not in
                     ('names','partial_red','partial_blue','conflict_edges','red_added',
                      'blue_added','added_edge_voltages')}))


if __name__ == '__main__':
    main()
