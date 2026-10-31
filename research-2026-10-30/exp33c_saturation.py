"""exp33c: split separable pairs into trivial ones (a singleton member f_a of N(e) has no b-coloured conflict, so
recolouring f_a alone frees a) and non-trivial ones (a genuine Kempe chain is needed).  The adversary minimises the
trivial count first (it saturates the singletons), then the non-trivial count.

Usage: exp33c_saturation.py
"""
import math
import random
import time

import networkx as nx

from exp33_kempe import K, l2_adj, separable, swap, component, load
from exp33b_adversary import colour_all_but, free
from graphs_hg import random_girth


def counts(adj, col, e):
    present = sorted({col[f] for f in adj[e]})
    if len(present) < K:
        return None
    triv = nontriv = 0
    nb = {f: {col[g] for g in adj[f]} for f in adj[e]}
    for i, a in enumerate(present):
        for b in present[i + 1:]:
            A = [f for f in adj[e] if col[f] == a]
            B = [f for f in adj[e] if col[f] == b]
            if (len(A) == 1 and b not in nb[A[0]]) or (len(B) == 1 and a not in nb[B[0]]):
                triv += 1
            elif separable(adj, col, e, a, b) is not None:
                nontriv += 1
    return triv, nontriv


def anneal2(adj, col, e, steps, rng):
    region = set(adj[e])
    for f in list(region):
        region.update(adj[f])
    region.discard(e)
    region = sorted(region)

    def E():
        c = counts(adj, col, e)
        if c is None:
            return 10 ** 6 + 1000 * (K - len({col[f] for f in adj[e]}))
        return 1000 * c[0] + c[1]

    cur = E()
    best = (cur, None)
    for t in range(steps):
        T = 3000 * (1 - t / steps) + 0.3
        f = rng.choice(region)
        old = list(col)
        if rng.random() < 0.5:
            fr = [c for c in free(adj, col, f) if c != col[f]]
            if not fr:
                continue
            col[f] = rng.choice(fr)
        else:
            c = rng.randrange(K)
            if c == col[f]:
                continue
            swap(col, component(adj, col, f, col[f], c), col[f], c)
        new = E()
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            if cur < best[0]:
                best = (cur, counts(adj, col, e))
        else:
            col[:] = old
    return best


if __name__ == "__main__":
    t0 = time.time()
    cases = [("n=13 #10760", list(load(13))[10760])]
    for n, g, s in ((60, 5, 0), (60, 5, 1), (200, 6, 0), (40, 3, 0)):
        G = random_girth(n, g, s) if g > 3 else nx.random_regular_graph(4, n, seed=s)
        cases.append((f"n={n} girth={nx.girth(G)} seed={s}", [tuple(x) for x in G.edges()]))
    for name, edges in cases:
        adj = l2_adj(edges)
        cand = [e for e in range(len(adj)) if len(adj[e]) >= 22]
        rng = random.Random(3)
        for e in rng.sample(cand, 2):
            col = colour_all_but(adj, e, rng)
            best = anneal2(adj, col, e, 20000, rng)
            print(f"{name} edge {e} d={len(adj[e])}: best (trivial, non-trivial) separable = {best[1]}  "
                  f"[{time.time() - t0:.0f}s]", flush=True)
