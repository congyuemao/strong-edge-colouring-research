"""Hub count behind the spanmax result of exp9 (replaces the pigeonhole-hard SAT runs).

For a triangle T = {e0,f,g} at each tree position and each e in T: the closures of e's zero-cost
classes are pairwise disjoint conflicting pairs {x,y} in N(e) \\ T (one pair per class), and
Lemma 2 needs at least 5 of them.  Under the (Phi1, Phi2, -span) minimum every closure of a compact
(span 4) triangle must itself give a compact triangle {e,x,y}.  We compute the maximum number of
disjoint admissible pairs by maximum matching."""
import itertools

import networkx as nx

from exp8_local_sat import Model, pair_types


def span(*edges):
    return len(set(v for e in edges for v in e))


M = Model(4, 2)
nb = {e: set(M.nbrs(e)) for e in M.E}
print(f"{'position':16s} {'span':>4s}   max # disjoint closures for e0 / f / g")
for name, (f, g) in pair_types().items():
    if g not in nb[f]:
        continue
    T = (( 0, 1), f, g)
    s0 = span(*T)
    row = []
    for e in T:
        cand = [n for n in nb[e] if n not in T]
        H = nx.Graph()
        for x, y in itertools.combinations(cand, 2):
            if y in nb[x] and (s0 == 5 or span(e, x, y) == 4):
                H.add_edge(x, y)
        row.append(len(nx.max_weight_matching(H, maxcardinality=True)))
    verdict = "impossible (< 5)" if min(row) < 5 else "possible"
    print(f"{name:16s} {s0:4d}   {row}   -> {verdict}")
