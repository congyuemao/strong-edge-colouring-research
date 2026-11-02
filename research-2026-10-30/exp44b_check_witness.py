"""exp44b: independent check of the exp44 SAT witnesses (both modes, every ball edge coloured).  From the colouring of
the tree ball alone: properness (conflicts from the vertex sets), e blocked, and whether T1, T2, T1', T2' are available.
Usage (run from this directory): exp44b_check_witness.py
"""
import sys
from collections import Counter

import exp44_local_repair as X
from exp33_kempe import K, l2_adj

for weak in (False, True):
    edges, col, dist = X.main(True, weak)
    ball = [h for h in dist]
    nb = {}
    for x, y in edges:
        nb.setdefault(x, set()).add(y)
        nb.setdefault(y, set()).add(x)

    def conflict(i, j):
        (a, b), (c, d) = edges[i], edges[j]
        return bool({a, b} & {c, d}) or any(t in nb[s] for s in (a, b) for t in (c, d))

    inb = set(ball)
    ok = all(not (col[i] == col[j] and col[i] >= 0 and conflict(i, j)) for i in ball for j in ball if i < j)
    adj = [[j for j in ball if j != i and conflict(i, j)] if dist[i] <= 2 else None for i in range(len(edges))]
    e = 0
    N = adj[e]
    assert sorted(N) == sorted(l2_adj(edges)[e])
    seen = lambda h: {col[g] for g in adj[h] if g != e and col[g] >= 0}
    blocked = {col[f] for f in N} == set(range(K))
    mult = Counter(col[f] for f in N)
    T1 = any(all(q not in seen(f) for f in N if col[f] == p) for p in range(K) for q in range(K) if q != p)
    T1w = any(all(len(seen(f)) < K - 1 for f in N if col[f] == p) for p in range(K))
    T2 = T2w = False
    for p in [c for c in range(K) if mult[c] == 1]:
        fp = next(f for f in N if col[f] == p)
        for a in range(K):
            if a == p:
                continue
            A = [g for g in adj[fp] if g != e and col[g] == a]
            if all(len(seen(g)) < K - 1 for g in A):
                T2w = True
            for b in range(K):
                if b not in (a, p) and all(b not in seen(g) for g in A):
                    T2 = True
    print(f"weak={weak}: proper {ok}, blocked {blocked}, profile {sorted(Counter(mult.values()).items())}, "
          f"T1 {T1}, T2 {T2}, T1' {T1w}, T2' {T2w}", flush=True)
