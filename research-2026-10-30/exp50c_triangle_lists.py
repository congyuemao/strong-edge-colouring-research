"""exp50c: independent numeric checks for NEW_DIRECTIONS 11.23 on connected 4-regular graphs, conflicts from vertex relations only.
(1) the bound d_T'(ab) <= sum_{w in R} t(w);
(2) triangle S: in a random greedy colouring of G - S, every outer edge has at least 20 - 15 = 5 free colours, the six
outer edges conflict pairwise, and greedy completion of the outer edges fails only if all six lists are one 5-set;
(3) K4 S: pendant edges have at most 12 coloured conflicts from G - S.
Usage: exp50c_triangle_lists.py n limit"""
import itertools
import random
import sys
import networkx as nx
from exp33_kempe import load
K = 20
n, limit = int(sys.argv[1]), int(sys.argv[2])
rng = random.Random(n)
gs = list(load(n))
rng.shuffle(gs)
gs = gs[:limit]
def conflict(nb, f, g):
    if set(f) & set(g):
        return True
    return bool((nb[f[0]] | nb[f[1]]) & set(g))
st = dict(graphs=0, edges=0, tri=0, minlist=99, equal5=0, k4=0, maxpend=0)
for edges in gs:
    edges = [tuple(e) for e in edges]
    G = nx.Graph(edges)
    nb = {v: set(G[v]) for v in G}
    st["graphs"] += 1
    non = [e for e in edges if not (nb[e[0]] & nb[e[1]])]
    t = {v: sum(v in e for e in non) for v in G}
    for f in non:
        R = (nb[f[0]] | nb[f[1]]) - set(f)
        d = sum(conflict(nb, f, g) for g in non if g != f)
        assert d <= sum(t[w] for w in R), (f, d)
        st["edges"] += 1
    tris = [c for c in nx.enumerate_all_cliques(G) if len(c) == 3]
    for S in rng.sample(tris, min(5, len(tris))):
        S = set(S)
        out = [e for e in edges if len(set(e) & S) == 1]
        if len(out) != 6:
            continue
        rest = [e for e in edges if not set(e) & S]
        rng.shuffle(rest)
        col = {}
        ok = True
        for e in rest:
            used = {col[g] for g in col if conflict(nb, e, g)}
            fr = [c for c in range(K) if c not in used]
            if not fr:
                ok = False
                break
            col[e] = rng.choice(fr)
        if not ok:
            continue
        for a, b in itertools.combinations(out, 2):
            assert conflict(nb, a, b)
        lists = [frozenset(range(K)) - {col[g] for g in col if conflict(nb, e, g)} for e in out]
        st["tri"] += 1
        st["minlist"] = min(st["minlist"], min(map(len, lists)))
        assert min(map(len, lists)) >= 5
        st["equal5"] += len(set(lists)) == 1 and len(lists[0]) == 5
    for c in nx.enumerate_all_cliques(G):
        if len(c) == 4:
            S = set(c)
            pend = [e for e in edges if len(set(e) & S) == 1]
            rest = [e for e in edges if not set(e) & S]
            for e in pend:
                st["maxpend"] = max(st["maxpend"], sum(conflict(nb, e, g) for g in rest))
            st["k4"] += 1
print(n, st)
assert st["maxpend"] <= 12
